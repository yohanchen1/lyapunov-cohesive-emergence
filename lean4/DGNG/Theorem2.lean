import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# 定理 2：轨迹有界性（能量下界）

E = -w·a·b + G(φ(x₁)) + G(φ(x₂)) + (α/2)·w²

由于 G(φ(xᵢ)) ≥ 0 且 |a|,|b| ≤ M，通过 Young 不等式可得：
    E ≥ (α/4)·w² - m·M⁴/(4α)
-/

open Real
open Set

/-!
## 引理 2a：G(φ(x)) ≥ 0

对 tanh 激活函数：G(u) = ∫₀ᵘ artanh(s) ds，
G(φ(x)) = x·tanh(x) - ln(cosh(x)) = x·tanh(x) + ln(1/cosh(x)) ≥ 0

### 微积分证明

令 f(t) = t·tanh(t) - ln(cosh(t))。
则 f'(t) = tanh(t) + t·sech²(t) - tanh(t) = t / cosh²(t).

- 对 t ≥ 0：f'(t) ≥ 0，故 f 在 [0,∞) 非减，f(0)=0 ⇒ f(x) ≥ 0.
- 对 x < 0：f 是偶函数，f(x) = f(-x) ≥ 0.
-/

/-- tanh 的导数：HasDerivAt tanh (1 / cosh²(t)) t -/
lemma hasDerivAt_tanh (t : ℝ) : HasDerivAt tanh (1 / ((Real.cosh t) ^ 2)) t := by
  have htanh_eq : tanh = (fun x : ℝ => Real.sinh x / Real.cosh x) := by
    ext x; exact Real.tanh_eq_sinh_div_cosh x
  rw [htanh_eq]
  have h_sinh : HasDerivAt sinh (Real.cosh t) t := hasDerivAt_sinh t
  have h_cosh : HasDerivAt cosh (Real.sinh t) t := hasDerivAt_cosh t
  have h_cosh_ne : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  have h_div := HasDerivAt.div h_sinh h_cosh h_cosh_ne
  -- h_div gives derivative: (cosh(t)·cosh(t) - sinh(t)·sinh(t)) / cosh²(t)
  -- Simplify numerator using cosh² - sinh² = 1
  have h_num : Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have h_deriv_eq : (Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t) / (Real.cosh t) ^ 2
                 = 1 / ((Real.cosh t) ^ 2) := by
    rw [h_num]
  exact h_div.congr_deriv h_deriv_eq

/-- f(t) = t·tanh(t) - ln(cosh(t)) 的导数 = t / cosh²(t) -/
lemma hasDerivAt_f (t : ℝ) : HasDerivAt (fun x : ℝ => x * tanh x - Real.log (Real.cosh x))
    (t / ((Real.cosh t) ^ 2)) t := by
  have h_id : HasDerivAt id (1 : ℝ) t := hasDerivAt_id t
  have h_tanh : HasDerivAt tanh (1 / ((Real.cosh t) ^ 2)) t := hasDerivAt_tanh t
  have h_mul : HasDerivAt (fun x : ℝ => x * tanh x)
      (1 * tanh t + t * (1 / ((Real.cosh t) ^ 2))) t :=
    HasDerivAt.mul h_id h_tanh
  have h_mul_simp : HasDerivAt (fun x : ℝ => x * tanh x) (tanh t + t / ((Real.cosh t) ^ 2)) t := by
    apply h_mul.congr_deriv
    ring
  -- HasDerivAt (log ∘ cosh) (sinh t / cosh t) t = HasDerivAt (log ∘ cosh) (tanh t) t
  have h_log_cosh : HasDerivAt (fun x : ℝ => Real.log (Real.cosh x)) (tanh t) t := by
    have h_cosh : HasDerivAt cosh (Real.sinh t) t := hasDerivAt_cosh t
    have h_cosh_ne : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
    have h_log := HasDerivAt.log h_cosh h_cosh_ne
    -- h_log gives derivative sinh t / cosh t = tanh t
    simpa [Real.tanh_eq_sinh_div_cosh] using h_log
  have h_sub : HasDerivAt (fun x : ℝ => x * tanh x - Real.log (Real.cosh x))
      ((tanh t + t / ((Real.cosh t) ^ 2)) - tanh t) t :=
    HasDerivAt.sub h_mul_simp h_log_cosh
  apply h_sub.congr_deriv
  ring

/-- f 是偶函数 -/
lemma f_even (t : ℝ) :
    t * tanh t - Real.log (Real.cosh t) = (-t) * tanh (-t) - Real.log (Real.cosh (-t)) := by
  simp [neg_mul, tanh_neg, cosh_neg]

/-- 能量非负部分：G(φ(x)) = x·tanh(x) - ln(cosh(x)) ≥ 0 -/
theorem Gphi_nonneg (x : ℝ) : x * tanh x + Real.log ((1 : ℝ) / Real.cosh x) ≥ 0 := by
  have hcosh_pos : Real.cosh x > 0 := Real.cosh_pos x
  have hlog : Real.log ((1 : ℝ) / Real.cosh x) = -Real.log (Real.cosh x) := by
    calc
      Real.log ((1 : ℝ) / Real.cosh x) = Real.log (1 : ℝ) - Real.log (Real.cosh x) :=
        Real.log_div (by norm_num) hcosh_pos.ne'
      _ = 0 - Real.log (Real.cosh x) := by rw [Real.log_one]
      _ = -Real.log (Real.cosh x) := by ring
  rw [hlog]
  -- 目标变为：x·tanh(x) + (-log(cosh(x))) ≥ 0，即 x·tanh(x) - log(cosh(x)) ≥ 0
  -- 用 ring 把 +(-b) 变成 -b，以便 set 能匹配
  ring_nf
  -- 现在目标是 x * tanh x - Real.log (Real.cosh x) ≥ 0，即 f x ≥ 0
  set f := fun (t : ℝ) => t * tanh t - Real.log (Real.cosh t) with hf
  set f' := fun (t : ℝ) => t / ((Real.cosh t) ^ 2) with hf'
  have hf0 : f 0 = 0 := by
    simp [f, Real.log_one, tanh_zero]
  have h0_mem : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (le_refl 0)
  have h_mono : MonotoneOn f (Ici (0 : ℝ)) := by
    -- 使用 monotoneOn_of_hasDerivWithinAt_nonneg
    have h_conv : Convex ℝ (Ici (0 : ℝ)) := convex_Ici 0
    have h_cont : ContinuousOn f (Ici (0 : ℝ)) := by
      intro t ht
      exact (hasDerivAt_f t).continuousAt.continuousWithinAt
    have h_deriv : ∀ t ∈ interior (Ici (0 : ℝ)),
        HasDerivWithinAt f (f' t) (interior (Ici (0 : ℝ))) t := by
      intro t ht
      exact (hasDerivAt_f t).hasDerivWithinAt
    have h_nonneg : ∀ t ∈ interior (Ici (0 : ℝ)), 0 ≤ f' t := by
      intro t ht
      rw [hf']
      have ht_pos : 0 < t := by
        -- interior (Ici 0) = Ioi 0
        rw [interior_Ici] at ht
        exact ht
      have hcosh_sq_pos : 0 < (Real.cosh t) ^ 2 := pow_pos (Real.cosh_pos t) 2
      exact div_nonneg ht_pos.le hcosh_sq_pos.le
    exact monotoneOn_of_hasDerivWithinAt_nonneg h_conv h_cont h_deriv h_nonneg
  by_cases hx : 0 ≤ x
  · -- x ≥ 0：单调性给出 f(0) ≤ f(x)
    have hx_mem : x ∈ Ici (0 : ℝ) := hx
    have hx_val : f 0 ≤ f x := h_mono h0_mem hx_mem hx
    rw [hf0] at hx_val
    exact hx_val
  · -- x < 0：偶性归约到 -x ≥ 0
    have hneg : 0 ≤ -x := by linarith
    have h_neg_mem : -x ∈ Ici (0 : ℝ) := hneg
    have h_neg_val : f 0 ≤ f (-x) := h_mono h0_mem h_neg_mem hneg
    rw [hf0] at h_neg_val
    have h_even : f x = f (-x) := by
      dsimp [f]
      rw [f_even x]
    have h_fx_nonneg : 0 ≤ f x := by linarith
    simpa [f] using h_fx_nonneg

/-!
## 引理 2b：能量下界（Young 不等式）

对任意 |a|, |b| ≤ 1, α > 0：
  -wab + (α/2)·w² ≥ (α/4)·w² - 1/α

证明：由 (α·w - 2ab)² ≥ 0 展开：
  α²w² - 4α·wab + 4(ab)² ≥ 0
  ⇒ wab ≤ (α/4)·w² + (ab)²/α ≤ (α/4)·w² + 1/α
  ⇒ -wab + (α/2)·w² ≥ (α/4)·w² - 1/α
-/

/-- Young 型不等式：由 (α·w - 2ab)² ≥ 0 配平方得到 -/
theorem young_bound (w a b α : ℝ) (hα : α > 0) : -w*a*b + (α/2)*w^2 ≥ (α/4)*w^2 - (a*b)^2/α := by
  have hsq := sq_nonneg (α*w - 2*a*b)
  have hsq_expanded : 0 ≤ α^2*w^2 - 4*α*w*a*b + 4*(a*b)^2 := by nlinarith
  have h_div : w*a*b ≤ (α/4)*w^2 + (a*b)^2/α := by
    have h_mul : 4*α*(w*a*b) ≤ α^2*w^2 + 4*(a*b)^2 := by nlinarith
    field_simp [hα.ne']
    nlinarith
  nlinarith

/-- 能量下界：对任意 |a|,|b| ≤ 1, α>0 -/
theorem energy_lower_bound (w a b α : ℝ)
    (ha : -1 ≤ a) (ha' : a ≤ 1) (hb : -1 ≤ b) (hb' : b ≤ 1) (hα : α > 0) :
    -w*a*b + (α/2)*w^2 ≥ (α/4)*w^2 - (1/α) := by
  have h_ab_sq_le_one : (a*b)^2 ≤ 1 := by
    have hab : -1 ≤ a*b := by
      nlinarith
    have hab' : a*b ≤ 1 := by
      nlinarith
    nlinarith
  have h_young : -w*a*b + (α/2)*w^2 ≥ (α/4)*w^2 - (a*b)^2/α :=
    young_bound w a b α hα
  have h_compare : (α/4)*w^2 - (a*b)^2/α ≥ (α/4)*w^2 - (1/α) := by
    have hdiv : (a*b)^2/α ≤ 1/α := by
      calc
        (a*b)^2/α = (a*b)^2 * (1/α) := by ring
        _ ≤ 1 * (1/α) := mul_le_mul_of_nonneg_right h_ab_sq_le_one (by positivity)
        _ = 1/α := by ring
    nlinarith
  nlinarith
