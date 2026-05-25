import Mathlib.Tactic

/-!
# 定理 3：平衡点的 δ-内聚划分特征（两节点核心）

## 记号延续两节点体系 (n=2, m=1)
- `a = φ(x₁)`, `b = φ(x₂)`: 激活值
- `a' = φ'(x₁)`, `b' = φ'(x₂)`: 激活函数导数
- `w`: 边 (1,2) 的权重
- `ε > 0`, `α > 0`: 学习率与衰减率

## 定理 3 的两节点版本

Part A (权重因子化)：
  在平衡点，w* = (1/α)·a·b
  —— 权重完全由节点激活值的乘积决定。

Part B (符号划分)：
  V⁺ = {i : φ(x_i*) > 0}, V⁻ = {i : φ(x_i*) < 0}, V⁰ = {i : φ(x_i*) = 0}
  两节点情形：退化但完整 —— 两节点可能都在 V⁺(正耦合)、
  都在 V⁻(正耦合)、异号(负耦合/拮抗)、或含零。

Part C (δ-内聚)：
  两节点退化为单个 δ 值，但结构仍然显现：
  同号 → w > 0 (内聚)，异号 → w < 0 (拮抗)，含零 → w = 0 (分离)。

Part D (自洽方程)：
  x₁* = (1/α)·a·b², x₂* = (1/α)·b·a²
  消去 w* 后的纯 x 方程组 —— 非线性耦合。
-/

open Real

/-!
## Part A：权重因子化

在平衡点，由定理 1 的 equilibrium condition：
  α·w = a·b  ⇒  w* = (1/α)·a·b
-/

/-- 定理 3 Part A：平衡点权重因子化 w* = (1/α)·a·b -/
theorem theorem3_factorization (w a b α : ℝ) (hα : α ≠ 0) (heq : α * w = a * b) :
    w = (1/α) * a * b := by
  field_simp [hα]
  nlinarith

/-- 更简洁的版本，使用 field_simp -/
theorem theorem3_factorization' (w a b α : ℝ) (hα : α ≠ 0) (heq : α * w = a * b) :
    w = a * b / α := by
  field_simp [hα]
  nlinarith

/-!
## Part B：符号划分

由 w* = a·b/α 和 α > 0，w* 的符号 = a·b 的符号。

同号 → w* > 0 (兴奋耦合/内聚)
异号 → w* < 0 (抑制耦合/拮抗)
含零 → w* = 0 (无耦合/分离)
-/

/-- 定理 3 Part B：同号 → w* > 0，即内聚耦合 -/
theorem theorem3_pos_coupling (w a b α : ℝ) (hα : α > 0) (heq : α * w = a * b)
    (ha : a > 0) (hb : b > 0) : w > 0 := by
  rw [theorem3_factorization' w a b α hα.ne' heq]
  have hab_pos : a * b > 0 := mul_pos ha hb
  exact div_pos hab_pos hα

/-- 定理 3 Part B：异号 → w* < 0，即拮抗耦合。
    w = a*b/α，其中 a>0, b<0 → a*b<0, α>0 → w<0 -/
theorem theorem3_neg_coupling (w a b α : ℝ) (hα : α > 0) (heq : α * w = a * b)
    (ha : a > 0) (hb : b < 0) : w < 0 := by
  have hab_neg : a * b < 0 := mul_neg_of_pos_of_neg ha hb
  rw [theorem3_factorization' w a b α hα.ne' heq]
  -- a*b < 0, α > 0 → (a*b)/α < 0
  exact (div_neg_iff.mpr (Or.inr ⟨hab_neg, hα⟩))

/-- 定理 3 Part B：含零 → w* = 0 -/
theorem theorem3_zero_coupling (w a b α : ℝ) (hα : α > 0) (heq : α * w = a * b)
    (ha0 : a = 0 ∨ b = 0) : w = 0 := by
  rcases ha0 with (ha0 | hb0)
  · rw [ha0] at heq; nlinarith
  · rw [hb0] at heq; nlinarith

/-!
## Part C：δ-内聚的退化两节点形式

在两节点情形，划分退化为：
  {V⁺, V⁻} 其中每组至多含一个节点。
但 δ-内聚的结构意义仍显现：
  同号 → 单一 δ = a·b/α > 0 (正内聚)
  异号 → 单一 δ = 0 (最大分离，因为 w<0≤0)

核心量：定义 δ := |w| 当同号，δ := 0 当异号/含零。
-/

/-- δ 值的定义（两节点退化版），直接由因子化公式计算，不依赖 w/α/heq -/
noncomputable def cohesive_delta (a b α : ℝ) : ℝ :=
  max (a * b / α) 0

/-- 内聚耦合：同号时 δ = w > 0 -/
theorem cohesive_delta_pos (w a b α : ℝ) (hα : α > 0) (heq : α * w = a * b)
    (ha : a > 0) (hb : b > 0) :
    cohesive_delta a b α = w := by
  have hw : w = a * b / α := theorem3_factorization' w a b α hα.ne' heq
  rw [hw]
  unfold cohesive_delta
  have hdiv_pos : a * b / α > 0 := by
    apply div_pos (mul_pos ha hb) hα
  exact max_eq_left hdiv_pos.le

/-!
## Part D：自洽方程

将 w* = a·b/α 代入平衡点条件 x₁ = w·b, x₂ = w·a：
  x₁* = (1/α)·a·b²
  x₂* = (1/α)·b·a²

这是两节点的自洽方程 —— 纯 φ(xᵢ) 的非线性耦合。
-/

/-- 定理 3 Part D：自洽方程 x₁* = (1/α)·a·b² -/
theorem theorem3_self_consistency_x1 (x₁ w a b α : ℝ) (hα : α ≠ 0)
    (heq_w : α * w = a * b) (heq_x : x₁ = w * b) : x₁ = (1/α) * a * b ^ 2 := by
  rw [theorem3_factorization w a b α hα heq_w] at heq_x
  rw [heq_x]
  ring

/-- 定理 3 Part D：自洽方程 x₂* = (1/α)·b·a² -/
theorem theorem3_self_consistency_x2 (x₂ w a b α : ℝ) (hα : α ≠ 0)
    (heq_w : α * w = a * b) (heq_x : x₂ = w * a) : x₂ = (1/α) * b * a ^ 2 := by
  rw [theorem3_factorization w a b α hα heq_w] at heq_x
  rw [heq_x]
  ring

/-!
## 推论：h(s) = s/φ(s) 的自洽形式

定义 h(s) = s/φ(s)。由 x₁* = a·b²/α 且 a = φ(x₁*)：
  x₁*/φ(x₁*) = b²/α
即 h(x₁*) = φ(x₂*)²/α —— 节点 1 的 h-值由节点 2 的激活平方决定。

在两节点情形这是平凡的（单边即邻域），但它预览了 n 节点版本：
  h(x_i*) = (1/α) Σ_{j∈N(i)} φ(x_j*)²
-/

/-- h 函数定义：h(s) = s/φ(s)，此处针对 tanh。
    注意：在 s=0 处 0/0 需人工延拓为 1（因 tanh'(0)=1）。
    实际形式化中建议用分段定义或 liminf 处理，此处仅作概念标记。 -/
noncomputable def h_func (s : ℝ) : ℝ :=
  if s = 0 then 1 else s / tanh s

/-!
## 自洽方程的对称形式

由 x₁* = a·b²/α, x₂* = b·a²/α，观察对称性：
  - 若 a = b → x₁* = x₂* = a³/α (对称平衡点)
  - 若 a = -b → x₁* = x₂* = -a³/α (反对称平衡点)
  - 若 a = 0 或 b = 0 → x₁* = x₂* = 0 (平凡平衡点)
-/

/-- 对称平衡点：a = b 时 x₁* = x₂* -/
theorem theorem3_symmetric_eq (x₁ x₂ w a b α : ℝ) (hα : α ≠ 0)
    (heq_w : α * w = a * b) (heq_x₁ : x₁ = w * b) (heq_x₂ : x₂ = w * a)
    (hab : a = b) : x₁ = x₂ := by
  rw [theorem3_self_consistency_x1 x₁ w a b α hα heq_w heq_x₁,
    theorem3_self_consistency_x2 x₂ w a b α hα heq_w heq_x₂, hab]

/-!
## 总结

定理 3 的两节点形式化核心结论：
  (1) 权重因子化：w* = a·b/α（Part A）
  (2) 符号决定耦合类型：同号→正(内聚), 异号→负(拮抗), 含零→零(分离)（Part B）
  (3) δ-内聚退化为单值但结构完整（Part C）
  (4) 自洽方程 x₁* = a·b²/α, x₂* = b·a²/α（Part D）

这些为 n 节点推广提供了代数核心 —— 所有证明均不依赖 φ 的具体形式，
仅依赖平衡点条件 α·w = a·b 和 x_i = w_ij·φ(x_j)。
-/
