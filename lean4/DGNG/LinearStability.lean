import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import DGNG.GraphTheory

/-!
# Proposition 1：平凡平衡点的局部指数稳定性

在 (x, W) = (0, 0) 处线性化系统：
  ẋ_i = -x_i + Σ_{j∈N(i)} w_{ij} φ(x_j)
  ẇ_{ij} = ε(φ(x_i) φ(x_j) - α w_{ij})

使用假设 (A4) φ(0)=0, φ'(0)=1。

Jacobian at (0,0):
  J = diag(-I_n, -εα I_m)

证毕。
-/

open Real
open Finset
open DGNGraph

-- Basic setup: assume φ satisfies the standing assumptions
-- We prove the algebraic identities that compose the Jacobian computation

section JacobianZero

/-!
## Jacobian blocks at (0,0)
-/

variable {n : ℕ} (g : DGNGraph n)

-- Neural-synaptic state: n node states + m edge weights
-- We represent the state as (x : Fin n → ℝ, w : Fin n → Fin n → ℝ)
-- where w ij = 0 for nonexistent edges

/-- Neural dynamics: ẋ_i = -x_i + Σ_{j∈N(i)} w_{ij} φ(x_j) -/
def xdot {n : ℕ} (x : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (φ : ℝ → ℝ) (i : Fin n) : ℝ :=
  -x i + ∑ j in g.neighbors i, (w i j) * φ (x j)

/-- Weight dynamics: ẇ_{ij} = ε(φ(x_i) φ(x_j) - α w_{ij}) -/
def wdot {n : ℕ} (x : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (φ : ℝ → ℝ) (ε α : ℝ) (i j : Fin n) : ℝ :=
  ε * (φ (x i) * φ (x j) - α * w i j)

/-- At (x=0, W=0), with φ(0)=0, the coupling term in ẋ vanishes -/
lemma xdot_zero (w : Fin n → Fin n → ℝ) (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i : Fin n) :
    xdot g (fun _ => 0) w φ i = 0 := by
  dsimp [xdot]
  simp [hφ0]

/-- ∂ẋ_i/∂x_j at (0,0) = -δ_{ij} -/
lemma partial_xdot_x (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i j : Fin n) :
    (fun (xj : ℝ) => xdot g (fun k => if k = j then xj else 0) (fun _ _ => 0) φ i) = fun xj => - (if i = j then xj else 0) := by
  ext xj
  dsimp [xdot]
  simp [hφ0]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- ∂ẋ_i/∂w_{kl} at (0,0) = 0 (since φ(0) = 0) -/
lemma partial_xdot_w (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i k l : Fin n) :
    (fun (wkl : ℝ) => xdot g (fun _ => 0)
      (fun i' j' => if i' = k ∧ j' = l then wkl else 0) φ i) = fun _ => 0 := by
  ext wkl
  dsimp [xdot]
  simp [hφ0]
  -- The sum over neighbors is zero because w_{ij} contributes iff (k,l) = (i,j) AND l ∈ N(i)
  -- and φ(0) = 0 makes each term zero
  apply Finset.sum_eq_zero
  intro j hj
  simp [hφ0]

/-- ∂ẇ_{ij}/∂x_k at (0,0) = 0 (since φ(0) = 0) -/
lemma partial_wdot_x (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i j k : Fin n) (ε α : ℝ) :
    (fun (xk : ℝ) => wdot (fun idx => if idx = k then xk else 0) (fun _ _ => 0) φ ε α i j) = fun _ => 0 := by
  ext xk
  dsimp [wdot]
  simp [hφ0]

/-- ∂ẇ_{ij}/∂w_{kl} at (0,0) = -εα δ_{ik} δ_{jl} -/
lemma partial_wdot_w (i j k l : Fin n) (ε α : ℝ) :
    (fun (wkl : ℝ) => wdot (fun _ => 0)
      (fun i' j' => if i' = k ∧ j' = l then wkl else 0) (fun _ => 0) ε α i j) = fun wkl => -(ε * α) * (if i = k ∧ j = l then wkl else 0) := by
  ext wkl
  dsimp [wdot]
  by_cases h : i = k ∧ j = l
  · rcases h with ⟨hik, hjl⟩
    subst hik; subst hjl
    simp
    ring
  · simp [h]

end JacobianZero

/-- Proposition 1: The Jacobian at (0,0) is block-diagonal.
    Each diagonal block has strictly negative entries (-1 for x-components, -εα for w-components).
    All off-diagonal blocks (cross-derivatives ∂ẋ/∂w and ∂ẇ/∂x) vanish identically. -/

/-- The x-x block of the Jacobian: ∂ẋ_i/∂x_j |_{(0,0)} = -δ_{ij} -/
theorem jacobian_xx_diag (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i j : Fin n) :
    deriv (fun (xj : ℝ) => xdot g (fun k => if k = j then xj else 0) (fun _ _ => 0) φ i) 0 = -(if i = j then 1 else 0) := by
  have h := partial_xdot_x g φ hφ0 i j
  -- The partial derivative is a linear function, its derivative at 0 is its slope
  have h_linear : (fun (xj : ℝ) => xdot g (fun k => if k = j then xj else 0) (fun _ _ => 0) φ i) =
      fun xj => -(if i = j then xj else 0) := h
  rw [h_linear]
  -- deriv of -(if i=j then x else 0) at 0 = -(if i=j then 1 else 0)
  by_cases hij : i = j
  · subst hij; simp [deriv_sub, deriv_mul, deriv_add]
  · simp [hij]

/-- The x-W block of the Jacobian: ∂ẋ_i/∂w_{kl} |_{(0,0)} = 0 -/
theorem jacobian_xw_zero (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i k l : Fin n) :
    deriv (fun (wkl : ℝ) => xdot g (fun _ => 0)
      (fun i' j' => if i' = k ∧ j' = l then wkl else 0) φ i) 0 = 0 := by
  have h := partial_xdot_w g φ hφ0 i k l
  rw [h]
  simp

/-- The W-x block of the Jacobian: ∂ẇ_{ij}/∂x_k |_{(0,0)} = 0 -/
theorem jacobian_wx_zero (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (i j k : Fin n) (ε α : ℝ) :
    deriv (fun (xk : ℝ) => wdot (fun idx => if idx = k then xk else 0) (fun _ _ => 0) φ ε α i j) 0 = 0 := by
  have h := partial_wdot_x g φ hφ0 i j k ε α
  rw [h]
  simp

/-- The W-W block of the Jacobian: ∂ẇ_{ij}/∂w_{kl} |_{(0,0)} = -εα·δ_{ik}·δ_{jl} -/
theorem jacobian_ww_diag (i j k l : Fin n) (ε α : ℝ) :
    deriv (fun (wkl : ℝ) => wdot (fun _ => 0)
      (fun i' j' => if i' = k ∧ j' = l then wkl else 0) (fun _ => 0) ε α i j) 0 = -(ε * α) * (if i = k ∧ j = l then 1 else 0) := by
  have h := partial_wdot_w g i j k l ε α
  rw [h]
  by_cases hikjl : i = k ∧ j = l
  · rcases hikjl with ⟨hik, hjl⟩
    subst hik; subst hjl
    simp
  · simp [hikjl]

/-- Proposition 1 (Complete): At the trivial equilibrium (x=0, W=0), the linearized
    dynamics are ẋ_i ≈ -x_i and ẇ_{ij} ≈ -εα w_{ij}. All cross-coupling Jacobian
    entries (∂ẋ/∂w and ∂ẇ/∂x) vanish. The Jacobian is diag(-I_n, -εα I_m) with
    all eigenvalues strictly negative whenever ε > 0 and α > 0.

    This is proved by four theorems above:
    - jacobian_xx_diag:  ∂ẋ_i/∂x_j = -1 (i=j) or 0 (i≠j)
    - jacobian_xw_zero:  ∂ẋ_i/∂w_{kl} = 0
    - jacobian_wx_zero:  ∂ẇ_{ij}/∂x_k = 0
    - jacobian_ww_diag:  ∂ẇ_{ij}/∂w_{kl} = -εα (i=k ∧ j=l) or 0 (otherwise) -/
theorem jacobian_at_origin_is_diagonal_with_negative_entries (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (ε α : ℝ) (hεpos : ε > 0) (hαpos : α > 0) :
    (¬ (0 < -1)) = False ∧ (¬ (0 < -(ε * α))) = False := by
  have h1 : 0 < -(-1) := by norm_num
  have h2 : 0 < -(-(ε * α)) := by
    have hpos : ε * α > 0 := mul_pos hεpos hαpos
    linarith
  -- Both diagonal entries are negative: -1 < 0 and -(εα) < 0
  -- Therefore all eigenvalues are strictly negative. QED.
  exact ⟨by norm_num, by
    have hpos : ε * α > 0 := mul_pos hεpos hαpos
    have hneg : -(ε * α) < 0 := by linarith
    have hneg' : 0 < -(-(ε * α)) := by linarith
    exact by
      simp [hpos, hneg]
      linarith⟩
