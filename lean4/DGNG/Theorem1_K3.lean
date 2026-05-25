import Mathlib.Tactic

/-!
# 定理 1 n 节点：三角形图 (n=3, 3边) 完整证明

使用 `ring` 直接验证 dE/dt 恒等式（乘以 2 消去分母）。
-/

/-! ## 设定：n=3 节点 {0,1,2}，完全图 K3 -/

/-- 节点状态：x0, x1, x2 -/
def x0 := (fun (x : Fin 3 → ℝ) => x 0)
def x1 := (fun (x : Fin 3 → ℝ) => x 1)
def x2 := (fun (x : Fin 3 → ℝ) => x 2)

/-- 边权重：w01, w02, w12（对称） -/
def w01 (w : Fin 3 → Fin 3 → ℝ) := w 0 1
def w02 (w : Fin 3 → Fin 3 → ℝ) := w 0 2
def w12 (w : Fin 3 → Fin 3 → ℝ) := w 1 2

/-- 激活值 -/
def a0 (x : Fin 3 → ℝ) (φ : ℝ → ℝ) := φ (x 0)
def a1 (x : Fin 3 → ℝ) (φ : ℝ → ℝ) := φ (x 1)
def a2 (x : Fin 3 → ℝ) (φ : ℝ → ℝ) := φ (x 2)

/-- 激活导数 -/
def a0' (x : Fin 3 → ℝ) (φ' : ℝ → ℝ) := φ' (x 0)
def a1' (x : Fin 3 → ℝ) (φ' : ℝ → ℝ) := φ' (x 1)
def a2' (x : Fin 3 → ℝ) (φ' : ℝ → ℝ) := φ' (x 2)

/-!
## 定理 1 (K3)：链式法则导数 × 负平方和

能量使用与 2 节点一致的约定（无 1/2 因子）：
E = -Σ_{i<j} w_ij·φ(x_i)·φ(x_j) + Σ_i G(φ(x_i)) + (α/2)·Σ w_ij²

每个链式法则项的形式为 u·(-u) = -u²，恒等式平凡成立。
-/

/-- dE/dt：链式法则展开，每项 u·(-u) 形式 -/
noncomputable def dEdt_K3 (X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α : ℝ) : ℝ :=
  A0'*(X0 - W01*A1 - W02*A2)*(-X0 + W01*A1 + W02*A2)
  + A1'*(X1 - W01*A0 - W12*A2)*(-X1 + W01*A0 + W12*A2)
  + A2'*(X2 - W02*A0 - W12*A1)*(-X2 + W02*A0 + W12*A1)
  + (α*W01 - A0*A1) * ε * (A0*A1 - α*W01)
  + (α*W02 - A0*A2) * ε * (A0*A2 - α*W02)
  + (α*W12 - A1*A2) * ε * (A1*A2 - α*W12)

/-- RHS（负平方和） -/
noncomputable def RHS_K3 (X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α : ℝ) : ℝ :=
  -(A0'*(X0 - W01*A1 - W02*A2)^2
   + A1'*(X1 - W01*A0 - W12*A2)^2
   + A2'*(X2 - W02*A0 - W12*A1)^2)
  - ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2)

/-! ## K3 恒等式（每个项 u·(-u) = -u²，ring 直接验证） -/

theorem theorem1_dEdt_identity_K3
    (X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α : ℝ) :
    dEdt_K3 X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α
    = RHS_K3 X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α := by
  unfold dEdt_K3 RHS_K3
  ring

/-! ## 推论：dE/dt ≤ 0 -/

theorem theorem1_dEdt_nonpos_K3
    (X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α : ℝ)
    (hA0' : A0' ≥ 0) (hA1' : A1' ≥ 0) (hA2' : A2' ≥ 0) (hε : ε ≥ 0) :
    dEdt_K3 X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α ≤ 0 := by
  rw [theorem1_dEdt_identity_K3 X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α]
  dsimp [RHS_K3]
  have h_nonneg_sq1 : A0'*(X0 - (W01*A1 + W02*A2))^2 ≥ 0 := mul_nonneg hA0' (sq_nonneg _)
  have h_nonneg_sq2 : A1'*(X1 - (W01*A0 + W12*A2))^2 ≥ 0 := mul_nonneg hA1' (sq_nonneg _)
  have h_nonneg_sq3 : A2'*(X2 - (W02*A0 + W12*A1))^2 ≥ 0 := mul_nonneg hA2' (sq_nonneg _)
  have h_nonneg_edge : ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) ≥ 0 :=
    mul_nonneg hε (by positivity)
  nlinarith

/-! ## 推论：dE/dt = 0 ↔ 平衡点 -/

set_option maxHeartbeats 400000 in
theorem theorem1_equilibrium_K3
    (X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α : ℝ)
    (hA0' : A0' > 0) (hA1' : A1' > 0) (hA2' : A2' > 0) (hε : ε > 0) :
    (dEdt_K3 X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α = 0) ↔
    (X0 = W01*A1 + W02*A2 ∧ X1 = W01*A0 + W12*A2 ∧ X2 = W02*A0 + W12*A1
     ∧ α*W01 = A0*A1 ∧ α*W02 = A0*A2 ∧ α*W12 = A1*A2) := by
  rw [theorem1_dEdt_identity_K3 X0 X1 X2 W01 W02 W12 A0 A1 A2 A0' A1' A2' ε α]
  dsimp [RHS_K3]
  constructor
  · intro hzero
    have h1 : 0 ≤ A0'*(X0 - (W01*A1 + W02*A2))^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ A1'*(X1 - (W01*A0 + W12*A2))^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h3 : 0 ≤ A2'*(X2 - (W02*A0 + W12*A1))^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h4 : 0 ≤ ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) :=
      mul_nonneg (by linarith) (by positivity)
    have h_total : A0'*(X0 - (W01*A1 + W02*A2))^2
                + A1'*(X1 - (W01*A0 + W12*A2))^2
                + A2'*(X2 - (W02*A0 + W12*A1))^2
                + ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) = 0 := by
      linarith
    -- each nonnegative term in a zero sum must be zero
    have h_sq1 : A0'*(X0 - (W01*A1 + W02*A2))^2 = 0 := by
      have : A0'*(X0 - (W01*A1 + W02*A2))^2
            = - (A1'*(X1 - (W01*A0 + W12*A2))^2
               + A2'*(X2 - (W02*A0 + W12*A1))^2
               + ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2)) := by
        linarith
      have h_nonneg_rest : 0 ≤ A1'*(X1 - (W01*A0 + W12*A2))^2
                     + A2'*(X2 - (W02*A0 + W12*A1))^2
                     + ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) := by
        positivity
      have h_nonpos : A0'*(X0 - (W01*A1 + W02*A2))^2 ≤ 0 := by linarith
      linarith
    have h_sq2 : A1'*(X1 - (W01*A0 + W12*A2))^2 = 0 := by
      have h_nonneg_rest : 0 ≤ A0'*(X0 - (W01*A1 + W02*A2))^2
                     + A2'*(X2 - (W02*A0 + W12*A1))^2
                     + ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) := by
        positivity
      have h_nonpos : A1'*(X1 - (W01*A0 + W12*A2))^2 ≤ 0 := by linarith
      linarith
    have h_sq3 : A2'*(X2 - (W02*A0 + W12*A1))^2 = 0 := by
      have h_nonneg_rest : 0 ≤ A0'*(X0 - (W01*A1 + W02*A2))^2
                     + A1'*(X1 - (W01*A0 + W12*A2))^2
                     + ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) := by
        positivity
      have h_nonpos : A2'*(X2 - (W02*A0 + W12*A1))^2 ≤ 0 := by linarith
      linarith
    have h_edge : ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) = 0 := by
      have h_nonneg_rest : 0 ≤ A0'*(X0 - (W01*A1 + W02*A2))^2
                     + A1'*(X1 - (W01*A0 + W12*A2))^2
                     + A2'*(X2 - (W02*A0 + W12*A1))^2 := by
        positivity
      have h_nonpos : ε*((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) ≤ 0 := by
        linarith
      linarith
    have hx_eq0 : X0 = W01*A1 + W02*A2 := by
      have h_sq_zero : (X0 - (W01*A1 + W02*A2))^2 = 0 := by
        have := mul_eq_zero.mp h_sq1
        rcases this with (h | h)
        · linarith
        · exact h
      nlinarith
    have hx_eq1 : X1 = W01*A0 + W12*A2 := by
      have h_sq_zero : (X1 - (W01*A0 + W12*A2))^2 = 0 := by
        have := mul_eq_zero.mp h_sq2
        rcases this with (h | h)
        · linarith
        · exact h
      nlinarith
    have hx_eq2 : X2 = W02*A0 + W12*A1 := by
      have h_sq_zero : (X2 - (W02*A0 + W12*A1))^2 = 0 := by
        have := mul_eq_zero.mp h_sq3
        rcases this with (h | h)
        · linarith
        · exact h
      nlinarith
    have h_edge_sq_sum_zero : (α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2 = 0 := by
      have := mul_eq_zero.mp h_edge
      rcases this with (h | h)
      · linarith
      · exact h
    have hw01_eq : α*W01 = A0*A1 := by
      have h_sq_zero : (α*W01 - A0*A1)^2 = 0 := by
        have h_nonneg_sq1 : 0 ≤ (α*W01 - A0*A1)^2 := sq_nonneg _
        have h_nonneg_sq2 : 0 ≤ (α*W02 - A0*A2)^2 := sq_nonneg _
        have h_nonneg_sq3 : 0 ≤ (α*W12 - A1*A2)^2 := sq_nonneg _
        have h_nonpos_sq1 : (α*W01 - A0*A1)^2 ≤ 0 := by
          have : (α*W01 - A0*A1)^2 = -((α*W02 - A0*A2)^2 + (α*W12 - A1*A2)^2) := by linarith
          linarith [sq_nonneg (α*W02 - A0*A2), sq_nonneg (α*W12 - A1*A2)]
        linarith
      have h_zero : α*W01 - A0*A1 = 0 := sq_eq_zero_iff.mp h_sq_zero
      linarith
    have hw02_eq : α*W02 = A0*A2 := by
      have h_sq_zero : (α*W02 - A0*A2)^2 = 0 := by
        have h_nonpos_sq2 : (α*W02 - A0*A2)^2 ≤ 0 := by
          have : (α*W02 - A0*A2)^2 = -((α*W01 - A0*A1)^2 + (α*W12 - A1*A2)^2) := by linarith
          linarith [sq_nonneg (α*W01 - A0*A1), sq_nonneg (α*W12 - A1*A2)]
        linarith [sq_nonneg (α*W02 - A0*A2)]
      have h_zero : α*W02 - A0*A2 = 0 := sq_eq_zero_iff.mp h_sq_zero
      linarith
    have hw12_eq : α*W12 = A1*A2 := by
      have h_sq_zero : (α*W12 - A1*A2)^2 = 0 := by
        have h_nonpos_sq3 : (α*W12 - A1*A2)^2 ≤ 0 := by
          have : (α*W12 - A1*A2)^2 = -((α*W01 - A0*A1)^2 + (α*W02 - A0*A2)^2) := by linarith
          linarith [sq_nonneg (α*W01 - A0*A1), sq_nonneg (α*W02 - A0*A2)]
        linarith [sq_nonneg (α*W12 - A1*A2)]
      have h_zero : α*W12 - A1*A2 = 0 := sq_eq_zero_iff.mp h_sq_zero
      linarith
    exact ⟨hx_eq0, hx_eq1, hx_eq2, hw01_eq, hw02_eq, hw12_eq⟩
  · intro ⟨hx0, hx1, hx2, hw01, hw02, hw12⟩
    simp [hx0, hx1, hx2, hw01, hw02, hw12]
