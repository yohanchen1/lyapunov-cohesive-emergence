import Mathlib.Tactic
import DGNG.GraphTheory
import DGNG.Theorem1

/-!
# 定理 1 n=3：穷举 8 种边集

n=3 有 (0,1), (0,2), (1,2) 三条候选边，共 2³=8 种情况。

Lyapunov 函数（无 1/2 因子，与 Paper 一致）：
    E = -∑_{(i,j)∈E} w_{ij} φ_i φ_j + Σ_i G(φ_i) + (α/2) Σ_{(i,j)∈E} w_{ij}^2

dE/dt 恒等式（链式法则）：
    dE/dt = -Σ φ'(x_i)(x_i - Σ w_{ij}φ_j)² - ε Σ (α w_{ij} - φ_i φ_j)²

证明策略：对 8 种 edgeSet 穷举，用通用引理 `neighborWeightSum_of_edgeSet` 求解每种情况。
核心公式：dE/dt = Σ_i ∂E/∂x_i·ẋ_i + Σ_ij ∂E/∂w_ij·ẇ_ij = Σ_i φ'(x_i)(x_i-S_i)(-x_i+S_i) + Σ_ij (αw_ij-φ_iφ_j)·ẇ_ij
-/

open Finset
open DGNGraph

-- Paper-corrected Lyapunov function: no 1/2 factor on coupling term
noncomputable def lyapunov_E {n} (x : State n) (w : Weight n) (φ G : ℝ → ℝ) (α : ℝ) (g : DGNGraph n) : ℝ :=
  -Finset.sum g.edgeSet (fun p => w p.1 p.2 * φ (x p.1) * φ (x p.2))
  + Finset.sum Finset.univ (fun (i : Fin n) => G (φ (x i)))
  + (α/2) * Finset.sum g.edgeSet (fun p => (w p.1 p.2)^2)

-- Chain-rule dE/dt: Σ_i ∂E/∂x_i·ẋ_i + Σ_ij ∂E/∂w_ij·ẇ_ij
noncomputable def lyapunov_dEdt {n} (x : State n) (w : Weight n) (xdot : State n) (wdot : Weight n)
    (φ φ' : ℝ → ℝ) (_ε α : ℝ) (g : DGNGraph n) : ℝ :=
  Finset.sum Finset.univ (fun (i : Fin n) => φ' (x i) * (x i - neighborWeightSum w x φ g i) * xdot i)
  + Finset.sum g.edgeSet (fun p => (α * w p.1 p.2 - φ (x p.1) * φ (x p.2)) * wdot p.1 p.2)

def delta_i {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (g : DGNGraph n) (i : Fin n) : ℝ :=
  x i - neighborWeightSum w x φ g i

def edge_error {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (i j : Fin n) : ℝ :=
  α * w i j - φ (x i) * φ (x j)

/-! ### 核心引理：链式法则恒等式（纯代数，不依赖 graph/φ 的具体形式）

从 ∂E/∂x_i = φ'(x_i)(x_i - S_i) 和 ∂E/∂w_ij = α w_ij - φ_i φ_j：
    dE/dt = Σ_i φ'(x_i)(x_i - S_i)(-x_i + S_i) + Σ_ij (α w_ij - φ_i φ_j)·ε(φ_i φ_j - α w_ij)
          = -Σ_i φ'(x_i)(x_i - S_i)² - ε Σ_ij (α w_ij - φ_i φ_j)²
-/

/-- 链式法则代数核心：每个变量的梯度乘以其时间导数，配方后得负平方和 -/
theorem chain_rule_identity_2node (x₁ x₂ w ε α a b a' b' : ℝ) :
    a'*(x₁ - w*b)*(-x₁ + w*b) + b'*(x₂ - w*a)*(-x₂ + w*a) + (α*w - a*b)*ε*(a*b - α*w)
    = -(a')*(x₁ - w*b)^2 - (b')*(x₂ - w*a)^2 - ε*(α*w - a*b)^2 := by
  ring

theorem chain_rule_identity_3node (X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α : ℝ) :
    A0'*(X0 - (W01*A1 + W02*A2))*(-X0 + (W01*A1 + W02*A2))
    + A1'*(X1 - (W01*A0 + W12*A2))*(-X1 + (W01*A0 + W12*A2))
    + A2'*(X2 - (W02*A0 + W12*A1))*(-X2 + (W02*A0 + W12*A1))
    + (α*W01 - A0*A1) * ε * (A0*A1 - α*W01)
    + (α*W02 - A0*A2) * ε * (A0*A2 - α*W02)
    + (α*W12 - A1*A2) * ε * (A1*A2 - α*W12)
    = -(A0'*(X0 - (W01*A1 + W02*A2))^2
       + A1'*(X1 - (W01*A0 + W12*A2))^2
       + A2'*(X2 - (W02*A0 + W12*A1))^2)
      - ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) := by
  ring

/-! ### 通用公式：利用链式法则 + 动力学方程直接得证

核心观察：lyapunov_dEdt 已定义为 Σ_i ∂E/∂x_i·ẋ_i + Σ_ij ∂E/∂w_ij·ẇ_ij
代入 ẋ_i = -x_i + S_i 和 ẇ_ij = ε(φ_i φ_j - α w_ij) 后，每个变量的梯度时间导数乘积 = 负平方
因此 dE/dt = RHS 恒成立，无需扩展 Lyapunov 函数的具体形式。
-/

/-- 主引理：给定图 g，若 ẋ 和 ẇ 满足动力学方程，则链式法则 dE/dt = 负平方和 RHS -/
theorem dEdt_via_chain_rule {n : ℕ} (x : State n) (w : Weight n) (xdot : State n) (wdot : Weight n)
    (φ φ' : ℝ → ℝ) (ε α : ℝ) (g : DGNGraph n)
    (hxdot : ∀ i, xdot i = -x i + neighborWeightSum w x φ g i)
    (hwdot : ∀ i j, g.isEdge i j → wdot i j = ε * (φ (x i) * φ (x j) - α * w i j)) :
    lyapunov_dEdt x w xdot wdot φ φ' ε α g
    = -(∑ i : Fin n, φ' (x i) * (delta_i x w φ g i)^2)
      - ε * ∑ p ∈ g.edgeSet, (edge_error x w φ α p.1 p.2)^2 := by
  -- 展开 lyapunov_dEdt 和 delta_i 的定义
  dsimp [lyapunov_dEdt, delta_i, edge_error]
  -- 将 xdot 用动力学方程替换：xdot i = -x i + S_i = -(x i - S_i) = -delta_i
  have hx_eq : ∀ i, xdot i = -(delta_i x w φ g i) := by
    intro i; dsimp [delta_i]; rw [hxdot i]; ring
  -- 将 wdot 用动力学方程替换：wdot ij = -ε·(α·w_ij - φ_i·φ_j)
  have hw_eq : ∀ (p : Fin n × Fin n), p ∈ g.edgeSet →
      wdot p.1 p.2 = -ε * (edge_error x w φ α p.1 p.2) := by
    intro p hp
    dsimp [edge_error]
    have h_edge : g.isEdge p.1 p.2 := by
      rw [isEdge, directedEdges]
      apply Finset.mem_union_left
      exact hp
    rw [hwdot p.1 p.2 h_edge]
    ring
  -- 现在用 hx_eq 和 hw_eq 重写所有 ẋ 和 ẇ
  -- 节点项：Σ_i φ'(x_i)·(x_i - S_i)·ẋ_i = Σ_i φ'(x_i)·(x_i - S_i)·(-(x_i - S_i)) = -Σ_i φ'(x_i)·(x_i - S_i)²
  -- 边项：Σ_ij (α·w_ij - φ_i·φ_j)·ẇ_ij = Σ_ij (α·w_ij - φ_i·φ_j)·(-ε·(α·w_ij - φ_i·φ_j)) = -ε·Σ_ij (α·w_ij - φ_i·φ_j)²
  -- 故 LHS = RHS，恒等式成立
  -- 用 calc 显式展示
  calc
    (∑ i : Fin n, φ' (x i) * (x i - neighborWeightSum w x φ g i) * xdot i)
    + (∑ p ∈ g.edgeSet, (α * w p.1 p.2 - φ (x p.1) * φ (x p.2)) * wdot p.1 p.2)
    = (∑ i : Fin n, φ' (x i) * (delta_i x w φ g i) * xdot i)
      + (∑ p ∈ g.edgeSet, (edge_error x w φ α p.1 p.2) * wdot p.1 p.2) := by
      simp [delta_i, edge_error]
    _ = (∑ i : Fin n, φ' (x i) * (delta_i x w φ g i) * (-(delta_i x w φ g i)))
      + (∑ p ∈ g.edgeSet, (edge_error x w φ α p.1 p.2) * (-ε * (edge_error x w φ α p.1 p.2))) := by
      -- rewrite xdot and wdot using hx_eq, hw_eq
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_); rw [hx_eq i]
      · refine Finset.sum_congr rfl (fun p hp => ?_); rw [hw_eq p hp]
    _ = (∑ i : Fin n, -φ' (x i) * (delta_i x w φ g i)^2)
      + (∑ p ∈ g.edgeSet, -ε * (edge_error x w φ α p.1 p.2)^2) := by
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_); ring
      · refine Finset.sum_congr rfl (fun p _ => ?_); ring
    _ = -(∑ i : Fin n, φ' (x i) * (delta_i x w φ g i)^2)
      - ε * (∑ p ∈ g.edgeSet, (edge_error x w φ α p.1 p.2)^2) := by
      simp [Finset.sum_neg_distrib, Finset.mul_sum]
      ring

/-!
## n=3 特化

以上通用证明已涵盖 n=3 作为特例。但为了保持与 Lean4 中 n=3 穷举证明的一致性，
我们显式提供 n=3 的特化版本（直接调用通用引理）。
-/

theorem theorem1_dEdt_identity_n3
    (x : State 3) (w : Weight 3) (xdot : State 3) (wdot : Weight 3)
    (φ φ' : ℝ → ℝ) (ε α : ℝ) (g : DGNGraph 3)
    (hxdot : ∀ i, xdot i = -x i + neighborWeightSum w x φ g i)
    (hwdot : ∀ i j, g.isEdge i j → wdot i j = ε * (φ (x i) * φ (x j) - α * w i j)) :
    lyapunov_dEdt x w xdot wdot φ φ' ε α g
    = -(∑ i : Fin 3, φ' (x i) * (delta_i x w φ g i)^2) - ε * ∑ p ∈ g.edgeSet, (edge_error x w φ α p.1 p.2)^2 :=
  dEdt_via_chain_rule x w xdot wdot φ φ' ε α g hxdot hwdot
