import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import DGNG.Theorem1
import DGNG.Theorem2

/-!
# LaSalle invariance principle and global convergence

Full chain: 3 axioms + 6 lemmas → main theorem.
-/

open Real
open Set
open Filter
open scoped Topology

/-! ## Axiom A: LaSalle invariance principle -/

axiom lasalle_convergence
  (F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ)
  (Vdot : ℝ × ℝ × ℝ → ℝ)
  (z : ℝ → ℝ × ℝ × ℝ)
  (hz_solution : ∀ t, HasDerivAt z (F (z t)) t)
  (Ω : Set (ℝ × ℝ × ℝ))
  (h_compact : IsCompact Ω)
  (h_forward_invariant : ∀ s ≥ 0, z s ∈ Ω)
  (h_Vdot_nonpos : ∀ p ∈ Ω, Vdot p ≤ 0)
  (h_Vdot_zero_iff : ∀ p ∈ Ω, Vdot p = 0 ↔ F p = 0) :
  ∀ x, ClusterPt x (map z atTop) → x ∈ ({p | F p = 0} ∩ Ω)

axiom lasalle_nonempty_intersection
  (F : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ)
  (Vdot : ℝ × ℝ × ℝ → ℝ)
  (z : ℝ → ℝ × ℝ × ℝ)
  (hz_solution : ∀ t, HasDerivAt z (F (z t)) t)
  (Ω : Set (ℝ × ℝ × ℝ))
  (h_compact : IsCompact Ω)
  (h_forward_invariant : ∀ s ≥ 0, z s ∈ Ω)
  (h_Vdot_nonpos : ∀ p ∈ Ω, Vdot p ≤ 0)
  (h_Vdot_zero_iff : ∀ p ∈ Ω, Vdot p = 0 ↔ F p = 0) :
  ({p | F p = 0} ∩ Ω).Nonempty

/-! ## DGNG 2-node system definitions -/

noncomputable def dgngF (ε α : ℝ) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun z =>
  (-z.1 + z.2.2 * tanh z.2.1, -z.2.1 + z.2.2 * tanh z.1,
   ε * (tanh z.1 * tanh z.2.1 - α * z.2.2))

noncomputable def dgngEnergy (α : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  -z.2.2 * tanh z.1 * tanh z.2.1
  + (z.1 * tanh z.1 - Real.log (Real.cosh z.1))
  + (z.2.1 * tanh z.2.1 - Real.log (Real.cosh z.2.1))
  + (α / 2) * z.2.2 ^ 2

noncomputable def dgngVdot (ε α : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  let a := tanh z.1; let b := tanh z.2.1; let w := z.2.2
  let a' := deriv tanh z.1; let b' := deriv tanh z.2.1
  (w * b - z.1) * a' * (z.1 - w * b) + (w * a - z.2.1) * b' * (z.2.1 - w * a) +
  (α * w - a * b) * ε * (a * b - α * w)

def equilibriumSet (α : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {z | z.1 = z.2.2 * tanh z.2.1 ∧ z.2.1 = z.2.2 * tanh z.1 ∧
       α * z.2.2 = tanh z.1 * tanh z.2.1}

/-! Helper: deriv tanh t = 1 / cosh² t > 0 -/

lemma deriv_tanh_pos (x : ℝ) : deriv tanh x > 0 := by
  rw [hasDerivAt_tanh x |>.deriv]
  positivity

lemma deriv_tanh_nonneg (x : ℝ) : 0 ≤ deriv tanh x := le_of_lt (deriv_tanh_pos x)

/-! ## Lemma 3: ∇V·F ≤ 0 -/

theorem vdot_nonpos (ε α : ℝ) (hε : ε ≥ 0) (z : ℝ × ℝ × ℝ) : dgngVdot ε α z ≤ 0 := by
  rcases z with ⟨x₁, x₂, w⟩
  dsimp [dgngVdot]
  rw [theorem1_dEdt_identity x₁ x₂ w ε α (tanh x₁) (tanh x₂) (deriv tanh x₁) (deriv tanh x₂)]
  have hd₁ := deriv_tanh_nonneg x₁
  have hd₂ := deriv_tanh_nonneg x₂
  nlinarith [sq_nonneg (x₁ - w * tanh x₂), sq_nonneg (x₂ - w * tanh x₁),
    sq_nonneg (α * w - tanh x₁ * tanh x₂)]

/-! ## Lemma 4: ∇V·F = 0 ↔ equilibrium -/

theorem vdot_eq_zero_iff (ε α : ℝ) (hε : ε > 0) (z : ℝ × ℝ × ℝ) :
    dgngVdot ε α z = 0 ↔ dgngF ε α z = (0, 0, 0) := by
  rcases z with ⟨x₁, x₂, w⟩
  dsimp [dgngVdot, dgngF]
  rw [theorem1_dEdt_identity x₁ x₂ w ε α (tanh x₁) (tanh x₂) (deriv tanh x₁) (deriv tanh x₂)]
  have hd₁ := deriv_tanh_pos x₁
  have hd₂ := deriv_tanh_pos x₂
  constructor
  · intro hzero
    have hsum : deriv tanh x₁ * (x₁ - w * tanh x₂)^2
              + deriv tanh x₂ * (x₂ - w * tanh x₁)^2
              + ε * (α*w - tanh x₁ * tanh x₂)^2 = 0 := by linarith
    have hn1 : 0 ≤ deriv tanh x₁ * (x₁ - w * tanh x₂)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hn2 : 0 ≤ deriv tanh x₂ * (x₂ - w * tanh x₁)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hn3 : 0 ≤ ε * (α*w - tanh x₁ * tanh x₂)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have ht1 : deriv tanh x₁ * (x₁ - w * tanh x₂)^2 = 0 := by nlinarith
    have ht2 : deriv tanh x₂ * (x₂ - w * tanh x₁)^2 = 0 := by nlinarith
    have ht3 : ε * (α*w - tanh x₁ * tanh x₂)^2 = 0 := by nlinarith
    have hsq1 : (x₁ - w * tanh x₂)^2 = 0 := (mul_eq_zero.mp ht1).resolve_left (by linarith)
    have hsq2 : (x₂ - w * tanh x₁)^2 = 0 := (mul_eq_zero.mp ht2).resolve_left (by linarith)
    have hsq3 : (α*w - tanh x₁ * tanh x₂)^2 = 0 := (mul_eq_zero.mp ht3).resolve_left (by linarith)
    have hx₁_diff : x₁ - w * tanh x₂ = 0 := eq_zero_of_pow_eq_zero hsq1
    have hx₂_diff : x₂ - w * tanh x₁ = 0 := eq_zero_of_pow_eq_zero hsq2
    have hw_diff : α*w - tanh x₁ * tanh x₂ = 0 := eq_zero_of_pow_eq_zero hsq3
    simp [show -x₁ + w * tanh x₂ = 0 by linarith,
          show -x₂ + w * tanh x₁ = 0 by linarith,
          show tanh x₁ * tanh x₂ - α*w = 0 by linarith]
  · intro hFzero
    have h₁ : -x₁ + w * tanh x₂ = 0 := by
      have := congrArg (fun t : ℝ × ℝ × ℝ => t.1) hFzero; simpa using this
    have h₂ : -x₂ + w * tanh x₁ = 0 := by
      have := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) hFzero; simpa using this
    have h₃ : ε*(tanh x₁ * tanh x₂ - α*w) = 0 := by
      have := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) hFzero; simpa using this
    have hw_eq : α*w = tanh x₁ * tanh x₂ := by
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h₃ with (hε0 | h_eq)
      · linarith
      · linarith
    simp [show x₁ - w * tanh x₂ = 0 by linarith,
          show x₂ - w * tanh x₁ = 0 by linarith,
          show α*w - tanh x₁ * tanh x₂ = 0 by linarith]

/-! ## Lemma B1: energy derivative along ODE solution (chain rule) -/

lemma energy_hasDerivAt (z : ℝ → ℝ × ℝ × ℝ) (ε α : ℝ)
    (hz_solution : ∀ t, HasDerivAt z (dgngF ε α (z t)) t) (t : ℝ) :
    HasDerivAt (dgngEnergy α ∘ z) (dgngVdot ε α (z t)) t := by
  -- unpack components at time t
  set x₁ := (z t).1 with hx₁_def
  set x₂ := (z t).2.1 with hx₂_def
  set w := (z t).2.2 with hw_def
  set a := tanh x₁ with ha_def
  set b := tanh x₂ with hb_def
  set a' := deriv tanh x₁ with ha'_def
  set b' := deriv tanh x₂ with hb'_def
  set F₁ := -x₁ + w * b with hF₁_def
  set F₂ := -x₂ + w * a with hF₂_def
  set F₃ := ε * (a * b - α * w) with hF₃_def
  -- component HasDerivAt from hz_solution: rewrite derivative as explicit triple then project
  -- ℝ × ℝ × ℝ = ℝ × (ℝ × ℝ), so: .fst → component 1, .snd.fst → component 2, .snd.snd → component 3
  have h_sol : HasDerivAt z (F₁, F₂, F₃) t := by
    simpa [dgngF, hF₁_def, hF₂_def, hF₃_def, ha_def, hb_def, hw_def] using hz_solution t
  have hder_z₁ : HasDerivAt (fun s : ℝ => (z s).1) F₁ t := h_sol.fst
  have hder_z₂ : HasDerivAt (fun s : ℝ => (z s).2.1) F₂ t := h_sol.snd.fst
  have hder_z₃ : HasDerivAt (fun s : ℝ => (z s).2.2) F₃ t := h_sol.snd.snd
  -- tanh ∘ z₁ and tanh ∘ z₂
  have hder_tanh_val : deriv tanh x₁ = ((Real.cosh x₁) ^ 2)⁻¹ := by
    simpa [one_div] using (hasDerivAt_tanh x₁).deriv
  have hder_tanh_val₂ : deriv tanh x₂ = ((Real.cosh x₂) ^ 2)⁻¹ := by
    simpa [one_div] using (hasDerivAt_tanh x₂).deriv
  have hder_tanh₁ : HasDerivAt (tanh ∘ fun s : ℝ => (z s).1) (a' * F₁) t := by
    have h := (hasDerivAt_tanh x₁).comp t hder_z₁
    simpa [ha'_def, hF₁_def, ha_def, hder_tanh_val] using h
  have hder_tanh₂ : HasDerivAt (tanh ∘ fun s : ℝ => (z s).2.1) (b' * F₂) t := by
    have h := (hasDerivAt_tanh x₂).comp t hder_z₂
    simpa [hb'_def, hF₂_def, hb_def, hder_tanh_val₂] using h
  -- Term2: G(x₁) = x₁*tanh(x₁) - log(cosh(x₁)), derivative = x₁/cosh²(x₁) = x₁*a'
  have hder_G₁ : HasDerivAt
      (fun s : ℝ => (z s).1 * tanh ((z s).1) - Real.log (Real.cosh ((z s).1)))
      ((x₁ * a') * F₁) t := by
    have h := (hasDerivAt_f x₁).comp t hder_z₁
    -- h: HasDerivAt ... ((x₁ / cosh(x₁)^2) * F₁) t
    -- a' = deriv tanh x₁ = (cosh x₁)^(-2), so x₁ * a' = x₁ / cosh(x₁)^2
    have h_rewrite : x₁ / ((Real.cosh x₁) ^ 2) = x₁ * a' := by
      rw [ha'_def, hder_tanh_val]
      ring
    simpa [h_rewrite, hF₁_def] using h
  -- Term3: G(x₂), symmetric
  have hder_G₂ : HasDerivAt
      (fun s : ℝ => (z s).2.1 * tanh ((z s).2.1) - Real.log (Real.cosh ((z s).2.1)))
      ((x₂ * b') * F₂) t := by
    have h := (hasDerivAt_f x₂).comp t hder_z₂
    have h_rewrite : x₂ / ((Real.cosh x₂) ^ 2) = x₂ * b' := by
      rw [hb'_def, hder_tanh_val₂]
      ring
    simpa [h_rewrite, hF₂_def] using h
  -- Term4: (α/2)*w², derivative = α*w*F₃
  have hder_w₂ : HasDerivAt (fun s : ℝ => (α/2) * (z s).2.2 ^ 2) (α * w * F₃) t := by
    have h_sq : HasDerivAt (fun s : ℝ => (z s).2.2 ^ 2) (2 * w * F₃) t := by
      simpa [hF₃_def, hw_def] using (hder_z₃.pow 2).congr_deriv (by ring)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (h_sq.const_mul (α/2)).congr_deriv (by ring)
  -- Term1: -z₃ * tanh(z₁) * tanh(z₂) = (-z₃ * tanh(z₁)) * tanh(z₂)
  have h_negz₃ : HasDerivAt (fun s : ℝ => -(z s).2.2) (-F₃) t := by
    simpa [hF₃_def] using hder_z₃.neg
  have h_prod_tmp : HasDerivAt (fun s : ℝ => (-(z s).2.2) * tanh ((z s).1))
      ((-F₃) * a + (-w) * (a' * F₁)) t :=
    HasDerivAt.mul h_negz₃ hder_tanh₁
  -- multiply by tanh(z₂)
  have hder_T1 : HasDerivAt (fun s : ℝ => (-(z s).2.2) * tanh ((z s).1) * tanh ((z s).2.1))
      (((-F₃) * a + (-w) * (a' * F₁)) * b + ((-w) * a) * (b' * F₂)) t :=
    HasDerivAt.mul h_prod_tmp hder_tanh₂
  -- sum all four terms: E(z(t)) = T1 + G(x₁) + G(x₂) + (α/2)*w²
  have hder_E : HasDerivAt (dgngEnergy α ∘ z)
      ((((-F₃) * a + (-w) * (a' * F₁)) * b + ((-w) * a) * (b' * F₂))
       + ((x₁ * a') * F₁) + ((x₂ * b') * F₂) + α * w * F₃) t := by
    have hsum1 := HasDerivAt.add hder_T1 hder_G₁
    have hsum2 := HasDerivAt.add hsum1 hder_G₂
    have hsum3 := HasDerivAt.add hsum2 hder_w₂
    exact hsum3
  -- algebraic simplification to dgngVdot using Theorem1 identity
  have h_simp : (((-F₃) * a + (-w) * (a' * F₁)) * b + ((-w) * a) * (b' * F₂))
               + ((x₁ * a') * F₁) + ((x₂ * b') * F₂) + α * w * F₃
             = dgngVdot ε α (z t) := by
    dsimp [dgngVdot, F₁, F₂, F₃, a, b, a', b']
    rw [theorem1_dEdt_identity x₁ x₂ w ε α (tanh x₁) (tanh x₂) (deriv tanh x₁) (deriv tanh x₂)]
    ring
  rw [h_simp] at hder_E
  exact hder_E

/-! ## Theorem B: energy non-increasing along solutions -/

theorem energy_non_increasing
    (z : ℝ → ℝ × ℝ × ℝ) (ε α : ℝ) (hε : ε ≥ 0) (_hα : α > 0)
    (hz_solution : ∀ t, HasDerivAt z (dgngF ε α (z t)) t) :
    ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → dgngEnergy α (z t₂) ≤ dgngEnergy α (z t₁) := by
  intro t₁ t₂ hle
  set f := -(dgngEnergy α ∘ z) with hf_def
  have hder_f (t : ℝ) : HasDerivAt f (-dgngVdot ε α (z t)) t := by
    dsimp [f]
    have h_neg := (energy_hasDerivAt z ε α hz_solution t).neg
    simpa using h_neg
  have h_deriv_nonneg (t : ℝ) : 0 ≤ -dgngVdot ε α (z t) := by
    have h_nonpos := vdot_nonpos ε α hε (z t)
    linarith
  have h_mono : Monotone f :=
    monotone_of_hasDerivAt_nonneg hder_f h_deriv_nonneg
  have h_f_noninc : f t₁ ≤ f t₂ := h_mono hle
  dsimp [f] at h_f_noninc
  linarith

/-! ## Lemma 5a: energy lower bound -/

theorem energy_lower_bound_2node (x₁ x₂ w α : ℝ) (hα : α > 0) :
    dgngEnergy α (x₁, x₂, w) ≥ (α/4) * w^2 - 1/α := by
  dsimp [dgngEnergy]
  have ha_low : -1 ≤ tanh x₁ := by linarith [abs_lt.mp (abs_tanh_lt_one x₁)]
  have ha_high : tanh x₁ ≤ 1 := by linarith [abs_lt.mp (abs_tanh_lt_one x₁)]
  have hb_low : -1 ≤ tanh x₂ := by linarith [abs_lt.mp (abs_tanh_lt_one x₂)]
  have hb_high : tanh x₂ ≤ 1 := by linarith [abs_lt.mp (abs_tanh_lt_one x₂)]
  have hmain : -w * tanh x₁ * tanh x₂ + (α/2)*w^2 ≥ (α/4)*w^2 - 1/α :=
    energy_lower_bound w (tanh x₁) (tanh x₂) α ha_low ha_high hb_low hb_high hα
  have hG_nonneg (x : ℝ) : 0 ≤ x * tanh x - Real.log (Real.cosh x) := by
    have hG := Gphi_nonneg x
    have hlog : Real.log ((1:ℝ)/Real.cosh x) = -Real.log (Real.cosh x) := by
      calc
        Real.log ((1:ℝ)/Real.cosh x) = Real.log 1 - Real.log (Real.cosh x) :=
          Real.log_div (by norm_num) (Real.cosh_pos x).ne'
        _ = -Real.log (Real.cosh x) := by norm_num
    rw [hlog] at hG; linarith
  have hg₁ : 0 ≤ x₁ * tanh x₁ - Real.log (Real.cosh x₁) := hG_nonneg x₁
  have hg₂ : 0 ≤ x₂ * tanh x₂ - Real.log (Real.cosh x₂) := hG_nonneg x₂
  linarith

/-! ## Lemma 5b: weight uniformly bounded -/

theorem weight_uniformly_bounded
    (z : ℝ → ℝ × ℝ × ℝ) (ε α : ℝ) (hε : ε ≥ 0) (hα : α > 0)
    (hz_solution : ∀ t, HasDerivAt z (dgngF ε α (z t)) t) :
    ∃ W_max : ℝ, 0 ≤ W_max ∧ ∀ t ≥ 0, |(z t).2.2| ≤ W_max := by
  let E₀ := dgngEnergy α (z 0)
  set R := max 0 ((4/α)*(E₀ + 1/α)) with hR_def
  set W_max := Real.sqrt R with hW_def
  have hR_nonneg : 0 ≤ R := le_max_left _ _
  have hW_nonneg : 0 ≤ W_max := Real.sqrt_nonneg _
  have hW_sq : W_max^2 = R := Real.sq_sqrt hR_nonneg
  refine ⟨W_max, hW_nonneg, fun t ht => ?_⟩
  have hE_noninc : dgngEnergy α (z t) ≤ E₀ := by
    have h := energy_non_increasing z ε α hε hα hz_solution 0 t (by linarith)
    simpa [E₀] using h
  let x₁ := (z t).1; let x₂ := (z t).2.1; let w := (z t).2.2
  have hE_lower : dgngEnergy α (x₁, x₂, w) ≥ (α/4)*w^2 - 1/α :=
    energy_lower_bound_2node x₁ x₂ w α hα
  have hE_eq : dgngEnergy α (z t) = dgngEnergy α (x₁, x₂, w) := rfl
  rw [hE_eq] at hE_noninc
  have hw_sq_bound : w^2 ≤ (4/α)*(E₀ + 1/α) := by
    have htemp : (α/4)*w^2 ≤ E₀ + 1/α := by linarith
    have hcalc : ((4/α):ℝ)*((α/4)*w^2) = w^2 := by
      field_simp [hα.ne']
    have : w^2 = ((4/α):ℝ)*((α/4)*w^2) := by rw [hcalc]
    rw [this]
    exact mul_le_mul_of_nonneg_left htemp (by positivity)
  have hw_sq_le_R : w^2 ≤ R := by
    have : w^2 ≤ (4/α)*(E₀ + 1/α) := hw_sq_bound
    have : (4/α)*(E₀ + 1/α) ≤ R := le_max_right _ _
    linarith
  have hw_sq_le_Wsq : w^2 ≤ W_max^2 := by rw [hW_sq]; exact hw_sq_le_R
  have h_abs_sq : (|w|)^2 ≤ W_max^2 := by
    calc (|w|)^2 = w^2 := by simp
    _ ≤ W_max^2 := hw_sq_le_Wsq
  have h_sqrt : Real.sqrt ((|w|)^2) ≤ Real.sqrt (W_max^2) := Real.sqrt_le_sqrt h_abs_sq
  rw [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq hW_nonneg] at h_sqrt
  simpa

/-! ## Theorem: state uniformly bounded (ISS barrier certificate) -/

theorem state_uniformly_bounded
    (z : ℝ → ℝ × ℝ × ℝ) (ε α : ℝ) (hε : ε ≥ 0) (hα : α > 0)
    (hz_solution : ∀ t, HasDerivAt z (dgngF ε α (z t)) t) :
    ∃ C_x : ℝ, 0 ≤ C_x ∧ ∀ t ≥ 0, |(z t).1| ≤ C_x ∧ |(z t).2.1| ≤ C_x := by
  -- Step 1: get weight bound
  rcases weight_uniformly_bounded z ε α hε hα hz_solution with ⟨W_max, hW_nonneg, hW_bound⟩
  -- Step 2: define C_x. ISS: |xᵢ(t)| ≤ max(|xᵢ(0)|, W_max) for all t ≥ 0
  set C_x := max (|(z 0).1|) (max (|(z 0).2.1|) W_max) with hCx_def
  have hCx_nonneg : 0 ≤ C_x := by
    rw [hCx_def]
    refine le_trans (abs_nonneg _) (le_max_left _ _)
  have hCx_ge_Wmax : W_max ≤ C_x := by
    rw [hCx_def]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hx₁₀_le_Cx : |(z 0).1| ≤ C_x := by
    rw [hCx_def]; exact le_max_left _ _
  have hx₂₀_le_Cx : |(z 0).2.1| ≤ C_x := by
    rw [hCx_def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  -- Step 3: coupling bound for t ≥ 0
  have h_couple₁_bound (t : ℝ) (ht : t ≥ 0) : |(z t).2.2 * tanh ((z t).2.1)| ≤ W_max := by
    calc
      |(z t).2.2 * tanh ((z t).2.1)| = |(z t).2.2| * |tanh ((z t).2.1)| := abs_mul _ _
      _ ≤ |(z t).2.2| * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact le_of_lt (abs_tanh_lt_one _)
      _ = |(z t).2.2| := by ring
      _ ≤ W_max := hW_bound t ht
  have h_couple₂_bound (t : ℝ) (ht : t ≥ 0) : |(z t).2.2 * tanh ((z t).1)| ≤ W_max := by
    calc
      |(z t).2.2 * tanh ((z t).1)| = |(z t).2.2| * |tanh ((z t).1)| := abs_mul _ _
      _ ≤ |(z t).2.2| * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact le_of_lt (abs_tanh_lt_one _)
      _ = |(z t).2.2| := by ring
      _ ≤ W_max := hW_bound t ht
  -- Step 4: ISS barrier via integrating factor.
  -- Let u(t) = eᵗ·(x(t) - W_max). Then u'(t) = eᵗ·(-x+g + x - W_max) = eᵗ·(g - W_max) ≤ 0.
  -- So u nonincreasing: u(s) ≤ u(0) → x(s) - W_max ≤ (x(0) - W_max)·e⁻ˢ.
  -- This gives x(s) ≤ max(x(0), W_max). Lower bound symmetric via v(t) = eᵗ·(x(t) + W_max).
  have h_state_bound (t : ℝ) (ht : t ≥ 0) : |(z t).1| ≤ C_x ∧ |(z t).2.1| ≤ C_x := by
    let x₁ := fun s : ℝ => (z s).1
    let x₂ := fun s : ℝ => (z s).2.1
    let wf := fun s : ℝ => (z s).2.2
    have hx₁_deriv (s : ℝ) : HasDerivAt x₁ (-x₁ s + wf s * tanh (x₂ s)) s := by
      have h := hz_solution s
      have hfst : HasDerivAt (fun s : ℝ => (z s).1) ((dgngF ε α (z s)).1) s := h.fst
      simpa [x₁, x₂, wf, dgngF] using hfst
    have hx₂_deriv (s : ℝ) : HasDerivAt x₂ (-x₂ s + wf s * tanh (x₁ s)) s := by
      have h := hz_solution s
      have hsnd : HasDerivAt (fun s : ℝ => (z s).2.1) ((dgngF ε α (z s)).2.1) s := h.snd.fst
      simpa [x₁, x₂, wf, dgngF] using hsnd
    -- ISS barrier lemma: if f' = -f + g, |g| ≤ W_max, then |f(s)| ≤ max(|f(0)|, W_max) for s ≥ 0
    have h_iss_bound (f g : ℝ → ℝ) (hderiv : ∀ τ, HasDerivAt f (-f τ + g τ) τ)
      (hg_bound : ∀ τ ≥ 0, |g τ| ≤ W_max) (s : ℝ) (hs : 0 ≤ s) : |f s| ≤ max (|f 0|) W_max := by
      set M := max (|f 0|) W_max with hM_def
      have hW_le_M : W_max ≤ M := le_max_right _ _
      have hf0abs_le_M : |f 0| ≤ M := le_max_left _ _
      have h_exp_s_pos : 0 < Real.exp s := Real.exp_pos s
      -- Helper: from |g| ≤ W_max, get g ≥ -W_max and g ≤ W_max
      have hg_ge (τ : ℝ) (hτ : 0 ≤ τ) : -W_max ≤ g τ :=
        (abs_le.mp (hg_bound τ hτ)).left
      have hg_le (τ : ℝ) (hτ : 0 ≤ τ) : g τ ≤ W_max :=
        (abs_le.mp (hg_bound τ hτ)).right
      -- Upper bound: u(τ) = exp(τ)·(f(τ) - M), prove u'(τ) ≤ 0 for τ ≥ 0
      set u := fun τ : ℝ => Real.exp τ * (f τ - M) with hu_def
      have hu_deriv (τ : ℝ) : HasDerivAt u (Real.exp τ * (g τ - M)) τ := by
        have he := Real.hasDerivAt_exp τ
        have hf_sub : HasDerivAt (fun τ => f τ - M) (-f τ + g τ) τ := by
          have htemp := (hderiv τ).sub (hasDerivAt_const (c := M) τ)
          simpa only [sub_zero] using htemp
        have h_mul := HasDerivAt.mul he hf_sub
        simpa [u] using h_mul.congr_deriv (by ring)
      have hu_deriv_nonpos (τ : ℝ) (hτ : 0 ≤ τ) : Real.exp τ * (g τ - M) ≤ 0 := by
        have hg_le_M : g τ ≤ M := le_trans (hg_le τ hτ) hW_le_M
        have h_nonpos : g τ - M ≤ 0 := by linarith
        have h_exp_nonneg : 0 ≤ Real.exp τ := le_of_lt (Real.exp_pos τ)
        exact mul_nonpos_of_nonneg_of_nonpos h_exp_nonneg h_nonpos
      have hu_s_le_u0 : u s ≤ u 0 := by
        by_cases hsz : s = 0
        · subst hsz; rfl
        · have hpos : 0 < s := by
            by_contra! hle
            have heq : s = 0 := by linarith
            exact hsz heq
          have hu_cont : ContinuousOn u (Set.Icc (0 : ℝ) s) := by
            intro τ hτ
            exact (hu_deriv τ).continuousAt.continuousWithinAt
          have hu_diff : DifferentiableOn ℝ u (Set.Ioo (0 : ℝ) s) := by
            intro τ hτ
            exact (hu_deriv τ).differentiableAt.differentiableWithinAt
          rcases exists_deriv_eq_slope u (a := 0) (b := s) hpos hu_cont hu_diff with ⟨ξ, hξ, hξ_eq⟩
          -- hξ_eq: deriv u ξ = (u s - u 0) / (s-0)
          -- hu_deriv ξ gives: deriv u ξ = Real.exp ξ * (g ξ - M)
          have h_deriv_u : deriv u ξ = Real.exp ξ * (g ξ - M) := (hu_deriv ξ).deriv
          have h_slope_eq : (u s - u 0) / (s - 0) = Real.exp ξ * (g ξ - M) := by
            rw [← h_deriv_u, hξ_eq]
          have hξ_nonneg : 0 ≤ ξ := by
            rcases hξ with ⟨hξl, hξr⟩; linarith
          have h_nonpos_at_ξ : Real.exp ξ * (g ξ - M) ≤ 0 := hu_deriv_nonpos ξ hξ_nonneg
          -- (u s - u 0)/(s-0) ≤ 0 and s > 0 → u s - u 0 ≤ 0
          have h_slope_nonpos : (u s - u 0) / (s - 0) ≤ 0 := by
            rw [h_slope_eq]; exact h_nonpos_at_ξ
          have h_sub_nonpos : u s - u 0 ≤ 0 := by
            by_contra! hpos_sub
            have : 0 < (u s - u 0) / (s - 0) :=
              div_pos hpos_sub (by simpa [sub_zero] using hpos)
            linarith
          linarith
      have hfupper : f s ≤ M := by
        rw [hu_def] at hu_s_le_u0
        -- exp(s)*(f(s) - M) ≤ f(0) - M
        have hineq : Real.exp s * (f s - M) ≤ f 0 - M := by
          simpa using hu_s_le_u0
        have hf0leM : f 0 ≤ M := le_trans (le_abs_self _) hf0abs_le_M
        -- f(0) - M ≤ 0, so exp(s)*(f(s)-M) ≤ 0 → f(s)-M ≤ 0
        have h_nonpos : f 0 - M ≤ 0 := by linarith
        have htemp : Real.exp s * (f s - M) ≤ 0 := by linarith
        have h_fs_le_M : f s ≤ M := by
          by_contra! h_gt
          have : 0 < Real.exp s * (f s - M) := mul_pos h_exp_s_pos (by linarith)
          linarith
        exact h_fs_le_M
      -- Lower bound: v(τ) = exp(τ)·(f(τ) + M), prove v'(τ) ≥ 0 for τ ≥ 0
      set v := fun τ : ℝ => Real.exp τ * (f τ + M) with hv_def
      have hv_deriv (τ : ℝ) : HasDerivAt v (Real.exp τ * (g τ + M)) τ := by
        have he := Real.hasDerivAt_exp τ
        have hf_add : HasDerivAt (fun τ => f τ + M) (-f τ + g τ) τ := by
          have htemp := (hderiv τ).add (hasDerivAt_const (c := M) τ)
          simpa only [add_zero] using htemp
        have h_mul := HasDerivAt.mul he hf_add
        simpa [v] using h_mul.congr_deriv (by ring)
      have hv_deriv_nonneg (τ : ℝ) (hτ : 0 ≤ τ) : 0 ≤ Real.exp τ * (g τ + M) := by
        have hg_ge_nM : -M ≤ g τ := by
          have : -W_max ≤ g τ := hg_ge τ hτ
          linarith
        have h_nonneg : 0 ≤ g τ + M := by linarith
        have h_exp_nonneg : 0 ≤ Real.exp τ := le_of_lt (Real.exp_pos τ)
        exact mul_nonneg h_exp_nonneg h_nonneg
      have hv_s_ge_v0 : v 0 ≤ v s := by
        by_cases hsz : s = 0
        · subst hsz; rfl
        · have hpos : 0 < s := by
            by_contra! hle
            have heq : s = 0 := by linarith
            exact hsz heq
          have hv_cont : ContinuousOn v (Set.Icc (0 : ℝ) s) := by
            intro τ hτ
            exact (hv_deriv τ).continuousAt.continuousWithinAt
          have hv_diff : DifferentiableOn ℝ v (Set.Ioo (0 : ℝ) s) := by
            intro τ hτ
            exact (hv_deriv τ).differentiableAt.differentiableWithinAt
          rcases exists_deriv_eq_slope v (a := 0) (b := s) hpos hv_cont hv_diff with ⟨ξ, hξ, hξ_eq⟩
          -- hξ_eq: deriv v ξ = (v s - v 0) / s
          have h_deriv_v : deriv v ξ = Real.exp ξ * (g ξ + M) := (hv_deriv ξ).deriv
          have h_slope_eq : (v s - v 0) / (s - 0) = Real.exp ξ * (g ξ + M) := by
            rw [← h_deriv_v, hξ_eq]
          have hξ_nonneg : 0 ≤ ξ := by
            rcases hξ with ⟨hξl, hξr⟩; linarith
          have h_nonneg_at_ξ : 0 ≤ Real.exp ξ * (g ξ + M) := hv_deriv_nonneg ξ hξ_nonneg
          -- (v s - v 0)/(s-0) ≥ 0 and s > 0 → v s - v 0 ≥ 0
          have h_slope_nonneg : 0 ≤ (v s - v 0) / (s - 0) := by
            rw [h_slope_eq]; exact h_nonneg_at_ξ
          have h_sub_nonneg : 0 ≤ v s - v 0 := by
            by_contra! h_neg_sub
            have : (v s - v 0) / (s - 0) < 0 :=
              div_neg_of_neg_of_pos h_neg_sub (by linarith [sub_zero s])
            linarith
          linarith
      have hflower : -M ≤ f s := by
        rw [hv_def] at hv_s_ge_v0
        -- exp(s)*(f(s) + M) ≥ f(0) + M
        have hineq : f 0 + M ≤ Real.exp s * (f s + M) := by
          simpa using hv_s_ge_v0
        have h_nM_le_f0 : -M ≤ f 0 := by
          have : -|f 0| ≤ f 0 := neg_abs_le _; linarith
        -- 0 ≤ f 0 + M, so 0 ≤ exp(s)*(f(s)+M) and exp(s)>0 → 0 ≤ f(s)+M → -M ≤ f(s)
        have h_nonneg : 0 ≤ f 0 + M := by linarith
        have htemp : 0 ≤ Real.exp s * (f s + M) := by linarith
        have h_fs_ge_nM : -M ≤ f s := by
          by_contra! h_lt
          have : Real.exp s * (f s + M) < 0 := mul_neg_of_pos_of_neg h_exp_s_pos (by linarith)
          linarith
        exact h_fs_ge_nM
      -- Combine: -M ≤ f(s) ≤ M ↔ |f(s)| ≤ M
      exact abs_le.mpr ⟨hflower, hfupper⟩
    have hx₁_bound : |x₁ t| ≤ max (|x₁ 0|) W_max :=
      h_iss_bound x₁ (fun s => wf s * tanh (x₂ s)) hx₁_deriv h_couple₁_bound t ht
    have hx₂_bound : |x₂ t| ≤ max (|x₂ 0|) W_max :=
      h_iss_bound x₂ (fun s => wf s * tanh (x₁ s)) hx₂_deriv h_couple₂_bound t ht
    have hx₁_Cx : |x₁ t| ≤ C_x := by
      rw [hCx_def]
      refine le_trans hx₁_bound ?_
      refine max_le_max (le_refl _) ?_
      exact le_max_right _ _
    have hx₂_Cx : |x₂ t| ≤ C_x := by
      rw [hCx_def]
      refine le_trans hx₂_bound ?_
      exact le_max_right _ _
    exact ⟨hx₁_Cx, hx₂_Cx⟩
  refine ⟨C_x, hCx_nonneg, h_state_bound⟩

/-! ## Lemma 6: compact positively invariant set Ω -/

lemma dgngEnergy_continuous (α : ℝ) : Continuous (dgngEnergy α) := by
  unfold dgngEnergy
  have h_logcosh_cont : Continuous (fun x : ℝ => Real.log (Real.cosh x)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (Real.continuousAt_log ((Real.cosh_pos x).ne')).comp continuous_cosh.continuousAt
  let ctanh : Continuous tanh :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_tanh x).continuousAt
  refine ((continuous_snd.snd.neg.mul (ctanh.comp continuous_fst)).mul
    (ctanh.comp continuous_snd.fst)).add ?_ |>.add ?_ |>.add ?_
  · -- z.1 * tanh z.1 - log(cosh z.1)
    refine Continuous.sub (continuous_fst.mul (ctanh.comp continuous_fst))
      (h_logcosh_cont.comp continuous_fst)
  · -- z.2.1 * tanh z.2.1 - log(cosh z.2.1)
    refine Continuous.sub (continuous_snd.fst.mul (ctanh.comp continuous_snd.fst))
      (h_logcosh_cont.comp continuous_snd.fst)
  · -- (α/2) * z.2.2^2
    refine continuous_const.mul (continuous_snd.snd.pow 2)

def Omega (α E₀ C_x W_max : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {z | dgngEnergy α z ≤ E₀ ∧ |z.1| ≤ C_x ∧ |z.2.1| ≤ C_x ∧ |z.2.2| ≤ W_max}

set_option maxHeartbeats 0 in
theorem omega_is_compact (α E₀ C_x W_max : ℝ) : IsCompact (Omega α E₀ C_x W_max) := by
  have h_prod : IsCompact (Icc (-C_x) C_x ×ˢ Icc (-C_x) C_x ×ˢ Icc (-W_max) W_max) :=
    IsCompact.prod isCompact_Icc (IsCompact.prod isCompact_Icc isCompact_Icc)
  have h_subset : Omega α E₀ C_x W_max ⊆ Icc (-C_x) C_x ×ˢ Icc (-C_x) C_x ×ˢ Icc (-W_max) W_max := by
    intro z hz
    rcases hz with ⟨hE, hx₁, hx₂, hw⟩
    rcases abs_le.mp hx₁ with ⟨hl₁, hr₁⟩
    rcases abs_le.mp hx₂ with ⟨hl₂, hr₂⟩
    rcases abs_le.mp hw with ⟨hlw, hrw⟩
    exact ⟨⟨hl₁, hr₁⟩, ⟨hl₂, hr₂⟩, ⟨hlw, hrw⟩⟩
  have h_closed : IsClosed (Omega α E₀ C_x W_max) := by
    have h1 : IsClosed {z : ℝ × ℝ × ℝ | dgngEnergy α z ≤ E₀} :=
      isClosed_le (dgngEnergy_continuous α) continuous_const
    have h2 : IsClosed {z : ℝ × ℝ × ℝ | |z.1| ≤ C_x} :=
      isClosed_le (continuous_abs.comp continuous_fst) continuous_const
    have h3 : IsClosed {z : ℝ × ℝ × ℝ | |z.2.1| ≤ C_x} :=
      isClosed_le (continuous_abs.comp continuous_snd.fst) continuous_const
    have h4 : IsClosed {z : ℝ × ℝ × ℝ | |z.2.2| ≤ W_max} :=
      isClosed_le (continuous_abs.comp continuous_snd.snd) continuous_const
    unfold Omega
    simp only [setOf_and]
    exact IsClosed.inter h1 (IsClosed.inter h2 (IsClosed.inter h3 h4))
  exact IsCompact.of_isClosed_subset h_prod h_closed h_subset

theorem omega_positively_invariant
    (z : ℝ → ℝ × ℝ × ℝ) (ε α : ℝ) (hε : ε ≥ 0) (hα : α > 0)
    (hz_solution : ∀ t, HasDerivAt z (dgngF ε α (z t)) t)
    (C_x W_max : ℝ)
    (hCx_bound : ∀ t ≥ 0, |(z t).1| ≤ C_x ∧ |(z t).2.1| ≤ C_x)
    (hW_bound : ∀ t ≥ 0, |(z t).2.2| ≤ W_max) :
    ∀ s ≥ 0, z s ∈ Omega α (dgngEnergy α (z 0)) C_x W_max := by
  intro s hs
  have hE_s : dgngEnergy α (z s) ≤ dgngEnergy α (z 0) :=
    energy_non_increasing z ε α hε hα hz_solution 0 s (by linarith)
  rcases hCx_bound s hs with ⟨hx₁, hx₂⟩
  exact ⟨hE_s, hx₁, hx₂, hW_bound s hs⟩

/-! ## Theorem 7: global convergence -/

theorem theorem2_global_convergence
    (z : ℝ → ℝ × ℝ × ℝ) (ε α : ℝ) (hε : ε > 0) (hα : α > 0)
    (hz_solution : ∀ t, HasDerivAt z (dgngF ε α (z t)) t) :
    ∀ x, ClusterPt x (map z atTop) → x ∈ equilibriumSet α := by
  -- Step 1: boundedness
  rcases weight_uniformly_bounded z ε α (by linarith) hα hz_solution with ⟨W_max, hW_nonneg, hW_bound⟩
  rcases state_uniformly_bounded z ε α (by linarith) hα hz_solution with ⟨C_x, hCx_nonneg, hX_bound⟩
  -- Step 2: compact positively invariant Ω
  let E₀ := dgngEnergy α (z 0)
  let Ω := Omega α E₀ C_x W_max
  have h_for_inv : ∀ s ≥ 0, z s ∈ Ω := by
    have h := omega_positively_invariant z ε α (by linarith) hα hz_solution C_x W_max hX_bound hW_bound
    intro s hs
    have hmem := h s hs
    dsimp [Ω, E₀]
    exact hmem
  have h_compact : IsCompact Ω := omega_is_compact α E₀ C_x W_max
  -- Step 3: verify LaSalle conditions
  let F := dgngF ε α
  let Vdot := dgngVdot ε α
  have h_Vdot_nonpos : ∀ p ∈ Ω, Vdot p ≤ 0 := fun p _ => vdot_nonpos ε α (by linarith) p
  have h_Vdot_zero_iff : ∀ p ∈ Ω, Vdot p = 0 ↔ F p = 0 := fun p _ => vdot_eq_zero_iff ε α hε p
  -- Step 4: apply LaSalle axiom (topological cluster point formulation)
  have h_conv_to_intersection :
      ∀ x, ClusterPt x (map z atTop) → x ∈ ({p | F p = 0} ∩ Ω) :=
    lasalle_convergence F Vdot z hz_solution Ω h_compact h_for_inv
      h_Vdot_nonpos h_Vdot_zero_iff
  -- Step 5: {F=0} ∩ Ω = equilibriumSet α ∩ Ω
  have h_eq_set : {p | F p = 0} ∩ Ω = equilibriumSet α ∩ Ω := by
    ext p; constructor
    · intro ⟨hF, hΩ⟩
      rcases p with ⟨x₁, x₂, w⟩
      dsimp [F, dgngF] at hF
      have hx₁ : -x₁ + w * tanh x₂ = 0 := by
        have := congrArg (fun t : ℝ×ℝ×ℝ => t.1) hF; simpa using this
      have hx₂ : -x₂ + w * tanh x₁ = 0 := by
        have := congrArg (fun t : ℝ×ℝ×ℝ => t.2.1) hF; simpa using this
      have hw_raw : ε*(tanh x₁ * tanh x₂ - α*w) = 0 := by
        have := congrArg (fun t : ℝ×ℝ×ℝ => t.2.2) hF; simpa using this
      have hw_eq : α*w = tanh x₁ * tanh x₂ := by
        rcases eq_zero_or_eq_zero_of_mul_eq_zero hw_raw with (hε0 | h_eq)
        · exfalso; linarith
        · linarith
      refine ⟨?_, hΩ⟩
      dsimp [equilibriumSet]
      exact ⟨by linarith, by linarith, hw_eq⟩
    · intro ⟨hEq, hΩ⟩
      rcases p with ⟨x₁, x₂, w⟩
      dsimp [equilibriumSet] at hEq
      rcases hEq with ⟨hx₁, hx₂, hw_eq⟩
      refine ⟨?_, hΩ⟩
      dsimp [F, dgngF]
      have h1 : -x₁ + w * tanh x₂ = 0 := by linarith
      have h2 : -x₂ + w * tanh x₁ = 0 := by linarith
      have h3 : ε*(tanh x₁ * tanh x₂ - α*w) = 0 := by
        rw [hw_eq]; ring
      simp [h1, h2, h3]
  -- Step 6: every cluster point of the trajectory lies in the equilibrium set
  intro x hx_cluster
  have hx_mem : x ∈ ({p | F p = 0} ∩ Ω) := h_conv_to_intersection x hx_cluster
  rw [h_eq_set] at hx_mem
  exact hx_mem.left
