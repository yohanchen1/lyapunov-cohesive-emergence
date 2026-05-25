import Mathlib.Tactic

/-!
# 定理 1：Lyapunov 函数的单调性（代数核心）

## 记号（两节点 n=2, m=1）
- `a = φ(x₁)`, `b = φ(x₂)`: 激活值
- `a' = φ'(x₁)`, `b' = φ'(x₂)`: 激活函数导数
- `w`: 边 (1,2) 的权重
- `ε > 0`: 学习率, `α > 0`: 衰减率
- 动力学:
    ẋ₁ = -x₁ + w·b
    ẋ₂ = -x₂ + w·a
    ẇ  = ε·(a·b - α·w)
- G 满足 G'(φ(x)) = φ⁻¹(φ(x)) = x，故 dG(φ(x))/dx = x·φ'(x)
- Lyapunov: E = -w·a·b + G(φ(x₁)) + G(φ(x₂)) + (α/2)·w²

dE/dt = (-w·b + x₁)·a'·ẋ₁ + (-w·a + x₂)·b'·ẋ₂ + (α·w - a·b)·ẇ

代入 ẋ₁, ẋ₂, ẇ 后，表达式配方为三项负平方和。

**关键洞察**：这是纯多项式恒等式——不依赖 φ 的具体形式！
-/

open Real

/-- 定理 1 代数核心：dE/dt 恒等于负平方和形式 -/
theorem theorem1_dEdt_identity (x₁ x₂ w ε α a b a' b' : ℝ) :
    (w*b - x₁)*a'*(x₁ - w*b) + (w*a - x₂)*b'*(x₂ - w*a) + (α*w - a*b)*ε*(a*b - α*w)
    = -(a')*(x₁ - w*b)^2 - (b')*(x₂ - w*a)^2 - ε*(α*w - a*b)^2 := by
  ring

/-- 推论 1：dE/dt ≤ 0（需要 a' ≥ 0, b' ≥ 0, ε ≥ 0） -/
theorem theorem1_dEdt_nonpos (x₁ x₂ w ε α a b a' b' : ℝ)
    (ha' : a' ≥ 0) (hb' : b' ≥ 0) (hε : ε ≥ 0) :
    (w*b - x₁)*a'*(x₁ - w*b) + (w*a - x₂)*b'*(x₂ - w*a) + (α*w - a*b)*ε*(a*b - α*w) ≤ 0 := by
  rw [theorem1_dEdt_identity x₁ x₂ w ε α a b a' b']
  have h1 : -a' * (x₁ - w*b)^2 ≤ 0 := by
    nlinarith [sq_nonneg (x₁ - w*b)]
  have h2 : -b' * (x₂ - w*a)^2 ≤ 0 := by
    nlinarith [sq_nonneg (x₂ - w*a)]
  have h3 : -ε * (α*w - a*b)^2 ≤ 0 := by
    nlinarith [sq_nonneg (α*w - a*b)]
  nlinarith

/-- 推论 2：dE/dt = 0 当且仅当系统处于平衡点 -/
theorem theorem1_equilibrium_condition (x₁ x₂ w ε α a b a' b' : ℝ)
    (ha' : a' > 0) (hb' : b' > 0) (hε : ε > 0) :
    ((w*b - x₁)*a'*(x₁ - w*b) + (w*a - x₂)*b'*(x₂ - w*a) + (α*w - a*b)*ε*(a*b - α*w) = 0)
    ↔ (x₁ = w*b ∧ x₂ = w*a ∧ α*w = a*b) := by
  constructor
  · intro hzero
    rw [theorem1_dEdt_identity x₁ x₂ w ε α a b a' b'] at hzero
    have hsum : a'*(x₁ - w*b)^2 + b'*(x₂ - w*a)^2 + ε*(α*w - a*b)^2 = 0 := by nlinarith
    have h1 : a'*(x₁ - w*b)^2 = 0 := by
      nlinarith [sq_nonneg (x₁ - w*b), sq_nonneg (x₂ - w*a), sq_nonneg (α*w - a*b)]
    have h2 : b'*(x₂ - w*a)^2 = 0 := by
      nlinarith [sq_nonneg (x₁ - w*b), sq_nonneg (x₂ - w*a), sq_nonneg (α*w - a*b)]
    have h3 : ε*(α*w - a*b)^2 = 0 := by
      nlinarith [sq_nonneg (x₁ - w*b), sq_nonneg (x₂ - w*a), sq_nonneg (α*w - a*b)]
    have hsq1 : (x₁ - w*b)^2 = 0 :=
      (mul_eq_zero.mp h1).resolve_left (by linarith)
    have hx1 : x₁ = w*b := sub_eq_zero.mp <| eq_zero_of_pow_eq_zero hsq1
    have hsq2 : (x₂ - w*a)^2 = 0 :=
      (mul_eq_zero.mp h2).resolve_left (by linarith)
    have hx2 : x₂ = w*a := sub_eq_zero.mp <| eq_zero_of_pow_eq_zero hsq2
    have hsq3 : (α*w - a*b)^2 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by linarith)
    have hw : α*w = a*b := sub_eq_zero.mp <| eq_zero_of_pow_eq_zero hsq3
    exact ⟨hx1, hx2, hw⟩
  · intro ⟨hx1, hx2, hw⟩
    rw [theorem1_dEdt_identity x₁ x₂ w ε α a b a' b', hx1, hx2, hw]
    ring
