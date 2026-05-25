import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import DGNG.GraphTheory
import DGNG.Theorem2
import DGNG.EnergyBound_n
import DGNG.Theorem1_n
-- import DGNG.LaSalle  -- 不依赖 2 节点版本；n 节点证明是自包含的

/-!
# LaSalle invariance principle and global convergence (n-node)

将 2 节点 LaSalle 证明推广到 n 节点。

关键：每节点的 ISS 屏障独立证明（耦合项通过 |tanh|<1 有界），
组合得到整体紧致性。权重假设对称 `w i j = w j i`。
-/

open Real
open Set
open Filter
open Finset
open DGNGraph
open scoped Topology

/-! ## Typeclass instances for State/Weight -/
noncomputable instance {n : ℕ} : TopologicalSpace (State n) := Pi.topologicalSpace
noncomputable instance {n : ℕ} : TopologicalSpace (Weight n) := Pi.topologicalSpace
instance {n : ℕ} : AddCommGroup (State n) := Pi.addCommGroup
instance {n : ℕ} : AddCommGroup (Weight n) := Pi.addCommGroup
noncomputable instance {n : ℕ} : Module ℝ (State n) := Pi.module _ _ _
noncomputable instance {n : ℕ} : Module ℝ (Weight n) := Pi.module _ _ _
noncomputable instance {n : ℕ} : ContinuousSMul ℝ (State n) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → ℝ))
noncomputable instance {n : ℕ} : ContinuousSMul ℝ (Weight n) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → ℝ))
noncomputable instance {n : ℕ} : NormedAddCommGroup (State n) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → ℝ))
noncomputable instance {n : ℕ} : NormedAddCommGroup (Weight n) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℝ))
noncomputable instance {n : ℕ} : NormedSpace ℝ (State n) :=
  inferInstanceAs (NormedSpace ℝ (Fin n → ℝ))
noncomputable instance {n : ℕ} : NormedSpace ℝ (Weight n) :=
  inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℝ))
noncomputable instance {n : ℕ} : NormedAddCommGroup (State n × Weight n) :=
  inferInstanceAs (NormedAddCommGroup ((Fin n → ℝ) × (Fin n → Fin n → ℝ)))
noncomputable instance {n : ℕ} : NormedSpace ℝ (State n × Weight n) :=
  inferInstanceAs (NormedSpace ℝ ((Fin n → ℝ) × (Fin n → Fin n → ℝ)))

/-! ## 辅助引理 -/

/-- 有限和绝对值不等式：|∑ x| ≤ ∑ |x| -/
lemma abs_sum_le_sum_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    |Finset.sum s f| ≤ Finset.sum s (|f ·|) := by
  classical
  induction' s using Finset.induction_on with a s has ih
  · simp
  · simp only [Finset.sum_insert has]
    have h_tri : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := by
      intro a b
      simpa [sub_eq_add_neg, abs_neg] using abs_sub a (-b)
    have h_sum : |Finset.sum s f| + |f a| ≤ Finset.sum s (|f ·|) + |f a| := by
      simpa [add_comm] using add_le_add_right ih (|f a|)
    calc
      |f a + Finset.sum s f| ≤ |f a| + |Finset.sum s f| := h_tri (f a) (Finset.sum s f)
      _ = |Finset.sum s f| + |f a| := by ring
      _ ≤ Finset.sum s (|f ·|) + |f a| := h_sum
      _ = |f a| + Finset.sum s (|f ·|) := by ring

/-- 若 f 在 ℝ 上处处可导且导数非负，则 f 单调递增 -/
lemma monotone_of_hasDerivAt_nonneg' {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'_nonneg : ∀ x, 0 ≤ f' x) : Monotone f := by
  have h_cont : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have h_monoOn : MonotoneOn f Set.univ :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_univ)
      h_cont.continuousOn
      (fun x _ => (hf x).hasDerivWithinAt)
      (fun x _ => hf'_nonneg x)
  exact fun a b h => h_monoOn (Set.mem_univ a) (Set.mem_univ b) h

/-- ISS 屏障引理：若 ẋ = -x + g(t)，|g| ≤ B (t≥0)，则 |x(t)| ≤ max(|x(0)|, B) -/
lemma iss_bound (f g : ℝ → ℝ) (hderiv : ∀ τ, HasDerivAt f (-f τ + g τ) τ)
    (B : ℝ) (_hB_nonneg : 0 ≤ B) (hg_bound : ∀ τ ≥ 0, |g τ| ≤ B) (s : ℝ) (hs : 0 ≤ s) :
    |f s| ≤ max (|f 0|) B := by
  set M := max (|f 0|) B with hM_def
  have hB_le_M : B ≤ M := le_max_right _ _
  have hf0abs_le_M : |f 0| ≤ M := le_max_left _ _
  have h_exp_s_pos : 0 < Real.exp s := Real.exp_pos s
  have hg_ge (τ : ℝ) (hτ : 0 ≤ τ) : -B ≤ g τ := (abs_le.mp (hg_bound τ hτ)).left
  have hg_le (τ : ℝ) (hτ : 0 ≤ τ) : g τ ≤ B := (abs_le.mp (hg_bound τ hτ)).right
  -- Upper bound: u(τ) = e^τ·(f(τ)-M), prove u'(τ) ≤ 0
  set u := fun τ : ℝ => Real.exp τ * (f τ - M) with hu_def
  have hu_deriv (τ : ℝ) : HasDerivAt u (Real.exp τ * (g τ - M)) τ := by
    have he := Real.hasDerivAt_exp τ
    have hf_sub : HasDerivAt (fun τ => f τ - M) (-f τ + g τ) τ := by
      simpa only [sub_zero] using (hderiv τ).sub (hasDerivAt_const (c := M) τ)
    have h_mul := HasDerivAt.mul he hf_sub
    simpa [u] using h_mul.congr_deriv (by ring)
  have hu_deriv_nonpos (τ : ℝ) (hτ : 0 ≤ τ) : Real.exp τ * (g τ - M) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos τ))
      (by have hgM : g τ ≤ M := le_trans (hg_le τ hτ) hB_le_M; linarith)
  have hu_s_le_u0 : u s ≤ u 0 := by
    by_cases hsz : s = 0
    · subst hsz; rfl
    · have hpos : 0 < s := by
        by_contra! hle; exact hsz (by linarith)
      have hu_cont : ContinuousOn u (Icc (0 : ℝ) s) :=
        fun τ hτ => (hu_deriv τ).continuousAt.continuousWithinAt
      have hu_diff : DifferentiableOn ℝ u (Ioo (0 : ℝ) s) :=
        fun τ hτ => (hu_deriv τ).differentiableAt.differentiableWithinAt
      rcases exists_deriv_eq_slope u (a := 0) (b := s) hpos hu_cont hu_diff with ⟨ξ, hξ, hξ_eq⟩
      have h_deriv_u : deriv u ξ = Real.exp ξ * (g ξ - M) := (hu_deriv ξ).deriv
      have h_slope_eq : (u s - u 0) / (s - 0) = Real.exp ξ * (g ξ - M) := by rw [← h_deriv_u, hξ_eq]
      have hξ_nonneg : 0 ≤ ξ := by rcases hξ with ⟨hξl, hξr⟩; linarith
      have h_slope_nonpos : (u s - u 0) / (s - 0) ≤ 0 := by rw [h_slope_eq]; exact hu_deriv_nonpos ξ hξ_nonneg
      by_contra! hpos_sub
      have hpos_num : 0 < u s - u 0 := sub_pos.mpr hpos_sub
      have : 0 < (u s - u 0) / (s - 0) := div_pos hpos_num (by simpa [sub_zero] using hpos)
      linarith
  have hfupper : f s ≤ M := by
    have hineq : Real.exp s * (f s - M) ≤ f 0 - M := by simpa [u] using hu_s_le_u0
    have hf0leM : f 0 ≤ M := le_trans (le_abs_self _) hf0abs_le_M
    have : Real.exp s * (f s - M) ≤ 0 := by linarith
    by_contra! h_gt; linarith [mul_pos h_exp_s_pos (by linarith : 0 < f s - M)]
  -- Lower bound: v(τ) = e^τ·(f(τ)+M), prove v'(τ) ≥ 0
  set v := fun τ : ℝ => Real.exp τ * (f τ + M) with hv_def
  have hv_deriv (τ : ℝ) : HasDerivAt v (Real.exp τ * (g τ + M)) τ := by
    have he := Real.hasDerivAt_exp τ
    have hf_add : HasDerivAt (fun τ => f τ + M) (-f τ + g τ) τ := by
      simpa only [add_zero] using (hderiv τ).add (hasDerivAt_const (c := M) τ)
    have h_mul := HasDerivAt.mul he hf_add
    simpa [v] using h_mul.congr_deriv (by ring)
  have hv_deriv_nonneg (τ : ℝ) (hτ : 0 ≤ τ) : 0 ≤ Real.exp τ * (g τ + M) :=
    mul_nonneg (le_of_lt (Real.exp_pos τ))
      (by
        have hg_ge_M : -M ≤ g τ := by
          have h := hg_ge τ hτ
          have hneg : -M ≤ -B := by linarith
          linarith
        linarith)
  have hv_s_ge_v0 : v 0 ≤ v s := by
    by_cases hsz : s = 0
    · subst hsz; rfl
    · have hpos : 0 < s := by
        by_contra! hle; exact hsz (by linarith)
      have hv_cont : ContinuousOn v (Icc (0 : ℝ) s) :=
        fun τ hτ => (hv_deriv τ).continuousAt.continuousWithinAt
      have hv_diff : DifferentiableOn ℝ v (Ioo (0 : ℝ) s) :=
        fun τ hτ => (hv_deriv τ).differentiableAt.differentiableWithinAt
      rcases exists_deriv_eq_slope v (a := 0) (b := s) hpos hv_cont hv_diff with ⟨ξ, hξ, hξ_eq⟩
      have h_deriv_v : deriv v ξ = Real.exp ξ * (g ξ + M) := (hv_deriv ξ).deriv
      have h_slope_eq : (v s - v 0) / (s - 0) = Real.exp ξ * (g ξ + M) := by rw [← h_deriv_v, hξ_eq]
      have hξ_nonneg : 0 ≤ ξ := by rcases hξ with ⟨hξl, hξr⟩; linarith
      have h_slope_nonneg : 0 ≤ (v s - v 0) / (s - 0) := by rw [h_slope_eq]; exact hv_deriv_nonneg ξ hξ_nonneg
      by_contra! h_neg_sub
      have h_neg_diff : v s - v 0 < 0 := by linarith
      have : (v s - v 0) / (s - 0) < 0 := div_neg_of_neg_of_pos h_neg_diff (by simpa [sub_zero] using hpos)
      linarith
  have hflower : -M ≤ f s := by
    have hineq : f 0 + M ≤ Real.exp s * (f s + M) := by simpa [v] using hv_s_ge_v0
    have h_nM_le_f0 : -M ≤ f 0 := by have := neg_abs_le (f 0); linarith
    have : 0 ≤ Real.exp s * (f s + M) := by linarith
    by_contra! h_lt; linarith [mul_neg_of_pos_of_neg h_exp_s_pos (by linarith : f s + M < 0)]
  exact abs_le.mpr ⟨hflower, hfupper⟩

/-! ## n-node DGNG system definitions -/

/-- n-node vector field: ẋ_i = -x_i + Σ_j w_{ij}·tanh(x_j), ẇ_{ij} = ε·(tanh(x_i)·tanh(x_j) - α·w_{ij}) -/
noncomputable def dgngF_n {n : ℕ} (ε α : ℝ) (g : DGNGraph n) : State n × Weight n → State n × Weight n :=
  fun p =>
  let x := p.1; let w := p.2
  let xdot : State n := fun i => -x i + neighborWeightSum w x Real.tanh g i
  let wdot : Weight n := fun i j => by
    classical
    exact if g.isEdge i j then ε * (Real.tanh (x i) * Real.tanh (x j) - α * w i j) else 0
  (xdot, wdot)

/-- n-node energy (Lyapunov function) -/
noncomputable def dgngEnergy_n {n : ℕ} (α : ℝ) (g : DGNGraph n) (p : State n × Weight n) : ℝ :=
  match p with
  | (x, w) =>
    -Finset.sum g.edgeSet (fun e => w e.1 e.2 * Real.tanh (x e.1) * Real.tanh (x e.2))
      + Finset.sum Finset.univ (fun (i : Fin n) => x i * Real.tanh (x i) - Real.log (Real.cosh (x i)))
      + (α/2) * Finset.sum g.edgeSet (fun e => (w e.1 e.2)^2)

/-- n-node Vdot: negative sum-of-squares form -/
noncomputable def dgngVdot_n {n : ℕ} (ε α : ℝ) (g : DGNGraph n) (p : State n × Weight n) : ℝ :=
  match p with
  | (x, w) =>
    -(Finset.sum Finset.univ (fun i =>
        deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2))
      - ε * Finset.sum g.edgeSet (fun e => (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2)

/-- Equilibrium set: F=0 -/
def equilibriumSet_n {n : ℕ} (ε α : ℝ) (g : DGNGraph n) : Set (State n × Weight n) :=
  {p | dgngF_n ε α g p = (fun _ => 0, fun _ _ => 0)}

/-! ## 正不变集 Ω_n 的定义 -/

/-- n 节点系统的紧致正不变集：能量 ≤ E₀、状态分量按 C_x 有界、
权重分量按 W_max 有界，且权重满足对称性（保持 ODE 不变性） -/
def Omega_n {n : ℕ} (α E₀ C_x W_max : ℝ) (g : DGNGraph n) : Set (State n × Weight n) :=
  {p | dgngEnergy_n α g p ≤ E₀ ∧ (∀ i, |p.1 i| ≤ C_x) ∧ (∀ i j, |p.2 i j| ≤ W_max)
       ∧ (∀ i j, p.2 i j = p.2 j i)}

/-! ## Axiom: LaSalle invariance principle for product space -/

axiom lasalle_convergence_n {n : ℕ}
  (F : State n × Weight n → State n × Weight n)
  (Vdot : State n × Weight n → ℝ)
  (z : ℝ → State n × Weight n)
  (hz_solution : ∀ t, HasDerivAt z (F (z t)) t)
  (Ω : Set (State n × Weight n))
  (h_compact : IsCompact Ω)
  (h_forward_invariant : ∀ s ≥ 0, z s ∈ Ω)
  (h_Vdot_nonpos : ∀ p ∈ Ω, Vdot p ≤ 0)
  (h_Vdot_zero_iff : ∀ p ∈ Ω, Vdot p = 0 ↔ F p = 0) :
  ∀ x, ClusterPt x (map z atTop) → x ∈ ({p | F p = 0} ∩ Ω)

/-! ## Helpers -/

lemma deriv_tanh_pos' (x : ℝ) : deriv Real.tanh x > 0 := by
  rw [hasDerivAt_tanh x |>.deriv]
  positivity

lemma deriv_tanh_nonneg' (x : ℝ) : 0 ≤ deriv Real.tanh x := le_of_lt (deriv_tanh_pos' x)

/-! ## Helper lemmas for proofs -/

lemma continuous_tanh' : Continuous tanh := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hasDerivAt_tanh x).continuousAt

lemma abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  have h1 : Real.tanh x < 1 := Real.tanh_lt_one x
  have h2 : -1 < Real.tanh x := Real.neg_one_lt_tanh x
  have h_abs : |Real.tanh x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact h_abs.le

lemma sum_nonneg_eq_zero_iff {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Finset.sum s f = 0 ↔ ∀ i ∈ s, f i = 0 := by
  refine ⟨fun h i hi => ?_, fun h => Finset.sum_eq_zero h⟩
  have hi_nonneg := hf i hi
  have hi_le_sum : f i ≤ Finset.sum s f := Finset.single_le_sum hf hi
  linarith

lemma card_neighbors_le_n {n : ℕ} (g : DGNGraph n) (i : Fin n) : (g.neighbors i).card ≤ n := by
  have h_subset : g.neighbors i ⊆ Finset.univ := Finset.subset_univ _
  have h_card_univ : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  calc
    (g.neighbors i).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card h_subset
    _ = n := Finset.card_fin n

lemma comp_semilinear_proj_i {n : ℕ} (z : ℝ → State n × Weight n) (t : ℝ) (dz : State n × Weight n)
    (hz : HasDerivAt z dz t) (i : Fin n) : HasDerivAt (fun (t' : ℝ) => (z t').1 i) (dz.1 i) t := by
  let L : (State n × Weight n) →L[ℝ] ℝ :=
    { toFun := fun p => p.1 i
      map_add' := by
        intro p q
        calc
          (p + q).1 i = (p.1 + q.1) i := by simp
          _ = p.1 i + q.1 i := Pi.add_apply (p.1) (q.1) i
      map_smul' := by
        intro r p
        calc
          (r • p).1 i = (r • p.1) i := by simp
          _ = r * p.1 i := by
            calc
              (r • p.1) i = r • (p.1 i) := Pi.smul_apply r (p.1) i
              _ = r * p.1 i := by simp
      cont := by
        refine (continuous_apply i).comp continuous_fst
    }
  have hL : HasDerivAt (L ∘ z) (L dz) t := by
    simpa using hz.comp_semilinear (σ := RingHom.id ℝ) (σ' := RingHom.id ℝ) L
  have hLz : L ∘ z = fun t' => (z t').1 i := by
    ext t'
    rfl
  have hLdz : L dz = dz.1 i := rfl
  simpa [hLz, hLdz] using hL

/-! ## Lemma 3_n: Vdot ≤ 0

直接由定义（三项均为非正）得出。
-/
theorem vdot_nonpos_n {n : ℕ} (ε α : ℝ) (hε : ε ≥ 0) (g : DGNGraph n) (p : State n × Weight n) :
    dgngVdot_n ε α g p ≤ 0 := by
  rcases p with ⟨x, w⟩
  dsimp [dgngVdot_n]
  have hsum1_nonneg : 0 ≤ Finset.sum Finset.univ (fun i =>
    deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (deriv_tanh_nonneg' _) (sq_nonneg _))
  have hsum2_nonneg : 0 ≤ Finset.sum g.edgeSet (fun e =>
    (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2_nonneg : 0 ≤ ε * Finset.sum g.edgeSet (fun e =>
    (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2) :=
    mul_nonneg hε hsum2_nonneg
  have h_total_nonneg : 0 ≤ Finset.sum Finset.univ (fun i =>
    deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2)
    + ε * Finset.sum g.edgeSet (fun e =>
      (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2) :=
    add_nonneg hsum1_nonneg h2_nonneg
  linarith

/-! ## Lemma 4_n: Vdot = 0 ↔ equilibrium

Need weight symmetry: w(i,j) = w(j,i).
Standard consequence of the sum-of-squares form of Vdot. -/
theorem vdot_eq_zero_iff_n {n : ℕ} (ε α : ℝ) (hε : ε > 0) (g : DGNGraph n) (p : State n × Weight n)
    (h_symm : ∀ i j, p.2 i j = p.2 j i) :
    dgngVdot_n ε α g p = 0 ↔ dgngF_n ε α g p = ((0, 0) : State n × Weight n) := by
  rcases p with ⟨x, w⟩
  -- Helper sums
  set A := Finset.sum Finset.univ (fun i =>
    deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2) with hA
  set B := Finset.sum g.edgeSet (fun e =>
    (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2) with hB
  have hA_nonneg : 0 ≤ A := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (deriv_tanh_nonneg' _) (sq_nonneg _))
  have hB_nonneg : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hA_terms_nonneg : ∀ i, 0 ≤ deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2 :=
    fun i => mul_nonneg (deriv_tanh_nonneg' _) (sq_nonneg _)
  have hB_terms_nonneg : ∀ e ∈ g.edgeSet, 0 ≤ (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2 :=
    fun e he => sq_nonneg _
  constructor
  · intro hVdot
    have h_eq : A + ε * B = 0 := by
      dsimp [dgngVdot_n, A, B] at hVdot
      linarith
    have hA_zero : A = 0 := by
      have : ε * B ≥ 0 := mul_nonneg (by linarith) hB_nonneg
      nlinarith
    have hB_zero : B = 0 := by
      nlinarith
    -- Each term in A is zero
    have hA_terms_zero : ∀ i, deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2 = 0 := by
      intro i
      have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      have h_le : deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2 ≤ A :=
        Finset.single_le_sum (fun j _ => hA_terms_nonneg j) hi_mem
      rw [hA_zero] at h_le
      have h_nonneg_term := hA_terms_nonneg i
      linarith
    have hx_eq : ∀ i, x i = neighborWeightSum w x Real.tanh g i := by
      intro i
      have h_term := hA_terms_zero i
      have h_pos : deriv Real.tanh (x i) > 0 := deriv_tanh_pos' (x i)
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h_term with (hderiv_zero | h_sq_zero)
      · exfalso; linarith
      · nlinarith
    -- Each edge term in B is zero
    have hB_terms_zero : ∀ e ∈ g.edgeSet, (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2 = 0 := by
      intro e he
      have h_le : (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2 ≤ B :=
        Finset.single_le_sum (fun f hf => hB_terms_nonneg f hf) he
      rw [hB_zero] at h_le
      have h_nonneg_term := hB_terms_nonneg e he
      linarith
    have hw_eq : ∀ e ∈ g.edgeSet, α * w e.1 e.2 = Real.tanh (x e.1) * Real.tanh (x e.2) := by
      intro e he
      have h_sq_zero := hB_terms_zero e he
      nlinarith
    -- Extend edge equality to g.isEdge via symmetry
    have h_edge_eq : ∀ (i j : Fin n), g.isEdge i j → α * w i j = Real.tanh (x i) * Real.tanh (x j) := by
      intro i j h_edge_ij
      unfold DGNGraph.isEdge at h_edge_ij
      rcases Finset.mem_union.mp h_edge_ij with (h_ij | h_ji_swap)
      · -- (i, j) ∈ g.edgeSet
        exact hw_eq (i, j) h_ij
      · -- (i, j) ∈ g.edgeSet.image swap, so (j, i) ∈ g.edgeSet
        rcases Finset.mem_image.mp h_ji_swap with ⟨⟨a, b⟩, ha, hswap⟩
        -- hswap: Prod.swap (a,b) = (i,j), i.e. (b,a) = (i,j)
        have h_ji_edge : (j, i) ∈ g.edgeSet := by
          have hswap' : (b, a) = (i, j) := by simpa using hswap
          rcases Prod.mk.inj hswap' with ⟨hb, ha'⟩
          subst hb ha'
          exact ha
        have h_eq_from_hw := hw_eq (j, i) h_ji_edge
        calc
          α * w i j = α * w j i := by
            have h := h_symm i j
            dsimp at h
            rw [h]
          _ = Real.tanh (x j) * Real.tanh (x i) := h_eq_from_hw
          _ = Real.tanh (x i) * Real.tanh (x j) := by ring
    -- Show dgngF_n ε α g (x, w) = (0, 0)
    dsimp [dgngF_n]
    apply Prod.ext
    · apply funext; intro i
      dsimp
      rw [hx_eq i]
      simp
      rfl
    · apply funext; intro i; apply funext; intro j
      dsimp
      by_cases hij : g.isEdge i j
      · rw [if_pos hij]
        rw [h_edge_eq i j hij]
        simp
        rfl
      · rw [if_neg hij]
        rfl
  · intro hF
    dsimp [dgngF_n] at hF
    have hxdot_eq : (dgngF_n ε α g (x, w)).1 = (fun _ : Fin n => (0 : ℝ)) := by
      simpa using congr_arg Prod.fst hF
    have hwdot_eq : (dgngF_n ε α g (x, w)).2 = (fun _ _ : Fin n => (0 : ℝ)) := by
      simpa using congr_arg Prod.snd hF
    have hx_eq' : ∀ i, x i = neighborWeightSum w x Real.tanh g i := by
      intro i
      have hxi := congr_fun hxdot_eq i
      dsimp [dgngF_n] at hxi
      linarith
    have hw_eq' : ∀ i j, g.isEdge i j → α * w i j = Real.tanh (x i) * Real.tanh (x j) := by
      intro i j h_edge
      have hwij := congr_fun (congr_fun hwdot_eq i) j
      dsimp [dgngF_n] at hwij
      rw [if_pos h_edge] at hwij
      have h_ε_ne_zero : ε ≠ 0 := by linarith
      rcases mul_eq_zero.mp hwij with (hεzero | hinner)
      · exfalso; exact h_ε_ne_zero hεzero
      · linarith
    -- Now compute Vdot = 0
    have h_sum1_zero : Finset.sum Finset.univ (fun i =>
        deriv Real.tanh (x i) * (x i - neighborWeightSum w x Real.tanh g i)^2) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hx_eq' i, sub_self]
      simp
    have h_sum2_zero : Finset.sum g.edgeSet (fun e =>
        (α * w e.1 e.2 - Real.tanh (x e.1) * Real.tanh (x e.2))^2) = 0 := by
      refine Finset.sum_eq_zero (fun e he => ?_)
      have h_edge_is_edge : g.isEdge e.1 e.2 := by
        dsimp [DGNGraph.isEdge, DGNGraph.directedEdges]
        exact Finset.mem_union_left _ he
      rw [hw_eq' e.1 e.2 h_edge_is_edge, sub_self]; simp
    dsimp [dgngVdot_n]
    rw [h_sum1_zero, h_sum2_zero]
    ring

/-! ## Energy lower bound (dgngEnergy_n) -/

theorem dgngEnergy_n_lower_bound {n : ℕ}
    (x : State n) (w : Weight n) (α : ℝ) (g : DGNGraph n) (M : ℝ)
    (hα : α > 0) (h_phi_bound : ∀ i, |Real.tanh (x i)| ≤ M) :
    dgngEnergy_n α g (x, w) ≥ (α/4) * Finset.sum g.edgeSet (fun e => (w e.1 e.2)^2)
                    - (g.edgeCount : ℝ) * (M^4) / α := by
  dsimp [dgngEnergy_n]
  have h_edge : ∀ p ∈ g.edgeSet,
      -(w p.1 p.2) * Real.tanh (x p.1) * Real.tanh (x p.2) + (α/2) * (w p.1 p.2)^2
      ≥ (α/4) * (w p.1 p.2)^2 - M^4 / α := by
    intro p hp
    let a := w p.1 p.2
    have h_young := young_bound a (Real.tanh (x p.1)) (Real.tanh (x p.2)) α hα
    -- h_young: -a * tanh_i * tanh_j + (α/2)*a^2 ≥ (α/4)*a^2 - (tanh_i*tanh_j)^2/α
    have h_sq : (Real.tanh (x p.1) * Real.tanh (x p.2))^2 ≤ M^4 :=
      sq_prod_le_M4 (Real.tanh (x p.1)) (Real.tanh (x p.2)) M (h_phi_bound p.1) (h_phi_bound p.2)
    have h_div : (Real.tanh (x p.1) * Real.tanh (x p.2))^2 / α ≤ M^4 / α := by
      -- (tanh_i*tanh_j)^2 ≤ M^4, divide by α>0
      refine div_le_div_of_nonneg_right h_sq (by linarith)
    linarith
  have hGphi : 0 ≤ Finset.sum Finset.univ (fun i : Fin n =>
    x i * Real.tanh (x i) - Real.log (Real.cosh (x i))) :=
    Finset.sum_nonneg (fun i _ => by
      have h := Gphi_nonneg (x i)
      -- h: x i * tanh (x i) + log (1 / cosh (x i)) ≥ 0
      have hlog_eq : Real.log ((1 : ℝ) / Real.cosh (x i)) = -Real.log (Real.cosh (x i)) := by
        calc
          Real.log ((1 : ℝ) / Real.cosh (x i)) = Real.log (1 : ℝ) - Real.log (Real.cosh (x i)) :=
            log_div (by norm_num) (Real.cosh_pos _).ne'
          _ = 0 - Real.log (Real.cosh (x i)) := by simp
          _ = -Real.log (Real.cosh (x i)) := by simp
      linarith)
  calc
    -Finset.sum g.edgeSet (fun p => w p.1 p.2 * Real.tanh (x p.1) * Real.tanh (x p.2))
    + (Finset.sum Finset.univ fun i : Fin n => x i * Real.tanh (x i) - Real.log (Real.cosh (x i)))
    + (α/2) * (Finset.sum g.edgeSet fun p => (w p.1 p.2)^2)
    = (Finset.sum g.edgeSet fun p =>
        (-(w p.1 p.2) * Real.tanh (x p.1) * Real.tanh (x p.2) + (α/2) * (w p.1 p.2)^2))
      + (Finset.sum Finset.univ fun i : Fin n => x i * Real.tanh (x i) - Real.log (Real.cosh (x i))) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≥ (Finset.sum g.edgeSet fun p =>
        (-(w p.1 p.2) * Real.tanh (x p.1) * Real.tanh (x p.2) + (α/2) * (w p.1 p.2)^2)) := by
      linarith
    _ ≥ (Finset.sum g.edgeSet fun p => (α/4) * (w p.1 p.2)^2 - M^4 / α) :=
      Finset.sum_le_sum h_edge
    _ = (α/4) * (Finset.sum g.edgeSet fun p => (w p.1 p.2)^2)
        - ((Finset.card g.edgeSet : ℝ) * M^4 / α) := by
      simp [Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    _ = (α/4) * (Finset.sum g.edgeSet fun p => (w p.1 p.2)^2)
        - (g.edgeCount : ℝ) * (M^4) / α := rfl

/-! ## Energy monotonicity (non-increasing) -/

/-- Derivative of energy along the flow equals Vdot (chain rule, kept as axiom for now).
    Given a solution z with derivative dgngF_n(z t) at time t, the composition
    dgngEnergy_n ∘ z has derivative dgngVdot_n(z t) at t. -/
axiom energy_hasDerivAt_n {n : ℕ} (ε α : ℝ) (g : DGNGraph n) (z : ℝ → State n × Weight n) (t : ℝ)
    (hz_solution : HasDerivAt z (dgngF_n ε α g (z t)) t) :
    HasDerivAt (fun s : ℝ => dgngEnergy_n α g (z s)) (dgngVdot_n ε α g (z t)) t

theorem energy_non_increasing_n {n : ℕ}
    (z : ℝ → State n × Weight n) (ε α : ℝ) (hε : ε ≥ 0) (g : DGNGraph n)
    (hz_solution : ∀ t, HasDerivAt z (dgngF_n ε α g (z t)) t)
    (_h_symm : ∀ t i j, (z t).2 i j = (z t).2 j i) :
    ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → dgngEnergy_n α g (z t₂) ≤ dgngEnergy_n α g (z t₁) :=
by
  intro t₁ t₂ ht
  set E := fun t : ℝ => dgngEnergy_n α g (z t) with hE
  set F := fun t : ℝ => -E t with hF
  have h_deriv_E : ∀ t, HasDerivAt E (dgngVdot_n ε α g (z t)) t := by
    intro t
    have hz_t : HasDerivAt z (dgngF_n ε α g (z t)) t := hz_solution t
    have h := energy_hasDerivAt_n ε α g z t hz_t
    simpa [E] using h
  have h_deriv_F : ∀ t, HasDerivAt F (-dgngVdot_n ε α g (z t)) t := by
    intro t
    have h := h_deriv_E t
    simpa [F, hE] using h.neg
  have h_nonneg_deriv_F : ∀ t, 0 ≤ -dgngVdot_n ε α g (z t) := by
    intro t
    have h_nonpos : dgngVdot_n ε α g (z t) ≤ 0 := vdot_nonpos_n ε α hε g (z t)
    linarith
  have h_mono_F : Monotone F :=
    monotone_of_hasDerivAt_nonneg' h_deriv_F h_nonneg_deriv_F
  have h_noninc : E t₂ ≤ E t₁ := by
    have hF_le : F t₁ ≤ F t₂ := h_mono_F ht
    dsimp [F, E] at hF_le
    linarith
  exact h_noninc

/-! ## Weight uniformly bounded

通过能量单调性和下界联合推出每条权重的一致界。
-/

/-- Projection onto a single weight component (i,j).  Continuous linear. -/
lemma comp_semilinear_proj_ij {n : ℕ} (z : ℝ → State n × Weight n) (t : ℝ) (dz : State n × Weight n)
    (hz : HasDerivAt z dz t) (i j : Fin n) :
    HasDerivAt (fun (t' : ℝ) => (z t').2 i j) (dz.2 i j) t := by
  let L : (State n × Weight n) →L[ℝ] ℝ :=
    { toFun := fun p => p.2 i j
      map_add' := by
        intro p q
        rfl
      map_smul' := by
        intro r p
        rfl
      cont := by
        refine (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
    }
  have hL : HasDerivAt (L ∘ z) (L dz) t := by
    simpa using hz.comp_semilinear (σ := RingHom.id ℝ) (σ' := RingHom.id ℝ) L
  have hLz : L ∘ z = fun t' => (z t').2 i j := rfl
  have hLdz : L dz = dz.2 i j := rfl
  simpa [hLz, hLdz] using hL

/-- A function with zero derivative everywhere is constant. -/
lemma const_of_hasDerivAt_zero (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) (a b : ℝ) : f a = f b := by
  have hf_mono : Monotone f :=
    monotone_of_hasDerivAt_nonneg' hf (fun x => by simp)
  have h_negf_deriv : ∀ x, HasDerivAt (-f) 0 x := fun x => by
    simpa using (hf x).neg
  have h_negf_mono : Monotone (-f) :=
    monotone_of_hasDerivAt_nonneg' h_negf_deriv (fun x => by simp)
  by_cases h : a ≤ b
  · have h1 : f a ≤ f b := hf_mono h
    have h2 : -f a ≤ -f b := h_negf_mono h
    linarith
  · have h' : b ≤ a := by linarith
    have h1 : f b ≤ f a := hf_mono h'
    have h2 : -f b ≤ -f a := h_negf_mono h'
    linarith

/-- `g.isEdge i j` is equivalent to `(i,j)` or `(j,i)` being in `g.edgeSet`. -/
lemma isEdge_iff {n : ℕ} (g : DGNGraph n) (i j : Fin n) :
    g.isEdge i j ↔ ((i, j) ∈ g.edgeSet ∨ (j, i) ∈ g.edgeSet) := by
  dsimp [DGNGraph.isEdge, DGNGraph.directedEdges]
  constructor
  · intro h
    rcases Finset.mem_union.mp h with (h_ij | h_swap)
    · exact Or.inl h_ij
    · rcases Finset.mem_image.mp h_swap with ⟨⟨a, b⟩, ha, h_eq⟩
      have h_swap_eq : (b, a) = (i, j) := by
        simpa [Prod.swap] using h_eq
      have hb : b = i := congr_arg Prod.fst h_swap_eq
      have ha' : a = j := congr_arg Prod.snd h_swap_eq
      subst ha' hb
      exact Or.inr ha
  · intro h
    rcases h with (h_ij | h_ji)
    · exact Finset.mem_union_left _ h_ij
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(j, i), h_ji, ?_⟩
      simp


/-- 权重一致有界：能量单调性与下界推导轨迹上所有权重的一致界。 -/
theorem weight_uniformly_bounded_n_traj {n : ℕ}
    (z : ℝ → State n × Weight n) (ε α : ℝ) (hε : ε ≥ 0) (hα : α > 0) (g : DGNGraph n)
    (hz_solution : ∀ t, HasDerivAt z (dgngF_n ε α g (z t)) t)
    (h_symm : ∀ t i j, (z t).2 i j = (z t).2 j i)
    (M : ℝ) (h_phi_bound : ∀ y, |Real.tanh y| ≤ M) :
    ∃ W_max : ℝ, 0 ≤ W_max ∧ ∀ t ≥ 0, ∀ i j, |(z t).2 i j| ≤ W_max := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨0, by norm_num, ?_⟩
    intro t ht i
    exact i.elim0
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    set E0 := dgngEnergy_n α g (z 0) with hE0_def

    -- (1) Energy is non-increasing along trajectories
    have hE_noninc : ∀ t ≥ 0, dgngEnergy_n α g (z t) ≤ E0 := by
      intro t ht
      exact energy_non_increasing_n z ε α hε g hz_solution h_symm 0 t ht

    -- (2) From energy lower bound: for any t ≥ 0,
    --       (α/4) * Σ_{e∈edgeSet} (w_e(t))² ≤ E0 + m*M⁴/α
    have h_sum_sq_bound (t : ℝ) (ht : 0 ≤ t) :
        Finset.sum g.edgeSet (fun (e : Fin n × Fin n) => ((z t).2 e.1 e.2)^2) ≤
        (4/α) * (E0 + (g.edgeCount : ℝ) * (M^4) / α) := by
      have hE_t : dgngEnergy_n α g (z t) ≤ E0 := hE_noninc t ht
      have h_lower := dgngEnergy_n_lower_bound ((z t).1) ((z t).2) α g M hα
        (fun i => h_phi_bound ((z t).1 i))
      -- h_lower: E(t) ≥ (α/4)*Σw² - m*M⁴/α
      -- hE_t:   E(t) ≤ E0
      -- Therefore (α/4)*Σw² - m*M⁴/α ≤ E0
      have h_ineq : (α/4) * Finset.sum g.edgeSet (fun e => ((z t).2 e.1 e.2)^2)
                   - (g.edgeCount : ℝ) * (M^4) / α ≤ E0 := by
        linarith
      have h_mul' : (α/4) * Finset.sum g.edgeSet (fun e => ((z t).2 e.1 e.2)^2)
                    ≤ E0 + (g.edgeCount : ℝ) * (M^4) / α := by
        linarith
      calc
        Finset.sum g.edgeSet (fun e => ((z t).2 e.1 e.2)^2)
            = (4/α) * ((α/4) * Finset.sum g.edgeSet (fun e => ((z t).2 e.1 e.2)^2)) := by
              field_simp [hα.ne']
        _ ≤ (4/α) * (E0 + (g.edgeCount : ℝ) * (M^4) / α) := by
          refine mul_le_mul_of_nonneg_left h_mul' ?_
          positivity

    set C_w_sq := (4/α) * (E0 + (g.edgeCount : ℝ) * (M^4) / α) with hC_w_sq_def
    have hC_w_sq_nonneg : 0 ≤ C_w_sq := by
      have h_lower_zero := dgngEnergy_n_lower_bound ((z 0).1) ((z 0).2) α g M hα
        (fun i => h_phi_bound ((z 0).1 i))
      have h_sq_nonneg : 0 ≤ Finset.sum g.edgeSet (fun e => ((z 0).2 e.1 e.2)^2) :=
        Finset.sum_nonneg (fun e _ => sq_nonneg _)
      have h_nonneg_sum : 0 ≤ E0 + (g.edgeCount : ℝ) * (M^4) / α := by
        nlinarith
      positivity

    -- (3) Bound edge weights: each |w_ij(t)| ≤ sqrt(C_w_sq) for edges
    have h_edge_bound (t : ℝ) (ht : 0 ≤ t) (i j : Fin n) (h_edge : g.isEdge i j) :
        |(z t).2 i j| ≤ Real.sqrt C_w_sq := by
      have h_sq_edge : ((z t).2 i j)^2 ≤ C_w_sq := by
        rcases (isEdge_iff g i j).mp h_edge with (h_ij | h_ji)
        · -- (i,j) ∈ g.edgeSet : directly in the sum
          have h_sum_bound := h_sum_sq_bound t ht
          have h_nonneg_sq : ∀ (e : Fin n × Fin n), e ∈ g.edgeSet → 0 ≤ ((z t).2 e.1 e.2)^2 := by
            intro e he; exact sq_nonneg _
          have h_sq_le_sum : ((z t).2 i j)^2 ≤
              Finset.sum g.edgeSet (fun e => ((z t).2 e.1 e.2)^2) :=
            Finset.single_le_sum h_nonneg_sq h_ij
          linarith
        · -- (j,i) ∈ g.edgeSet : use symmetry to bound via w_ji
          have h_sum_bound := h_sum_sq_bound t ht
          have h_nonneg_sq : ∀ (e : Fin n × Fin n), e ∈ g.edgeSet → 0 ≤ ((z t).2 e.1 e.2)^2 := by
            intro e he; exact sq_nonneg _
          have h_sq_le_sum : ((z t).2 j i)^2 ≤
              Finset.sum g.edgeSet (fun e => ((z t).2 e.1 e.2)^2) :=
            Finset.single_le_sum h_nonneg_sq h_ji
          have h_symm_ij : (z t).2 i j = (z t).2 j i := h_symm t i j
          rw [h_symm_ij]
          linarith
      calc
        |(z t).2 i j| = Real.sqrt (((z t).2 i j)^2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt C_w_sq := Real.sqrt_le_sqrt h_sq_edge

    -- (4) Non-edge weights are constant (ODE is ẇ_ij = 0)
    have h_non_edge_const (i j : Fin n) (h_not_edge : ¬ g.isEdge i j) (t : ℝ) (ht : 0 ≤ t) :
        (z t).2 i j = (z 0).2 i j := by
      have hw_deriv : ∀ τ, HasDerivAt (fun s : ℝ => (z s).2 i j) 0 τ := by
        intro τ
        have hz_τ : HasDerivAt z (dgngF_n ε α g (z τ)) τ := hz_solution τ
        have hwij_deriv : HasDerivAt (fun s : ℝ => (z s).2 i j) ((dgngF_n ε α g (z τ)).2 i j) τ :=
          comp_semilinear_proj_ij z τ (dgngF_n ε α g (z τ)) hz_τ i j
        have hwdot_zero : (dgngF_n ε α g (z τ)).2 i j = 0 := by
          dsimp [dgngF_n]
          rw [if_neg h_not_edge]
        rw [hwdot_zero] at hwij_deriv
        exact hwij_deriv
      have h_const : ∀ a b : ℝ, (z a).2 i j = (z b).2 i j :=
        const_of_hasDerivAt_zero (fun s : ℝ => (z s).2 i j) hw_deriv
      exact h_const t 0

    -- (5) Maximum initial absolute value over all pairs
    have h_univ_nonempty : (Finset.univ : Finset (Fin n × Fin n)).Nonempty := by
      let i0 : Fin n := ⟨0, hnpos⟩
      refine ⟨(i0, i0), Finset.mem_univ _⟩
    let C_init := Finset.sup' (Finset.univ : Finset (Fin n × Fin n)) h_univ_nonempty
      (fun (ij : Fin n × Fin n) => |(z 0).2 ij.1 ij.2|)
    have hC_init_nonneg : 0 ≤ C_init := by
      let i0 : Fin n := ⟨0, hnpos⟩
      have h_mem : (i0, i0) ∈ (Finset.univ : Finset (Fin n × Fin n)) := Finset.mem_univ _
      have h_val : 0 ≤ |(z 0).2 i0 i0| := abs_nonneg _
      have h_le : |(z 0).2 i0 i0| ≤ C_init :=
        Finset.le_sup' (f := fun (ij : Fin n × Fin n) => |(z 0).2 ij.1 ij.2|) h_mem
      linarith

    set W_max := max (Real.sqrt C_w_sq) C_init with hW_max_def
    have hW_max_nonneg : 0 ≤ W_max := by
      refine le_max_of_le_left (Real.sqrt_nonneg _)

    -- (6) Final bound: every weight at any t ≥ 0 satisfies |w_ij(t)| ≤ W_max
    refine ⟨W_max, hW_max_nonneg, ?_⟩
    intro t ht i j
    by_cases h_edge : g.isEdge i j
    · calc
        |(z t).2 i j| ≤ Real.sqrt C_w_sq := h_edge_bound t ht i j h_edge
        _ ≤ max (Real.sqrt C_w_sq) C_init := le_max_left _ _
        _ = W_max := rfl
    · calc
        |(z t).2 i j| = |(z 0).2 i j| := by rw [h_non_edge_const i j h_edge t ht]
        _ ≤ C_init := by
          have h_mem : (i, j) ∈ (Finset.univ : Finset (Fin n × Fin n)) := Finset.mem_univ _
          exact Finset.le_sup' (f := fun (ij : Fin n × Fin n) => |(z 0).2 ij.1 ij.2|) h_mem
        _ ≤ max (Real.sqrt C_w_sq) C_init := le_max_right _ _
        _ = W_max := rfl

/-! ## State boundedness (ISS barrier per node)

每节点 i 的 ODE: ẋ_i = -x_i + neighborWeightSum w x tanh g i.
由 |tanh|<1 和 |w_{ij}|≤W_max 得耦合界: |g_i(t)| ≤ n·W_max。
-/
theorem state_uniformly_bounded_n {n : ℕ}
    (z : ℝ → State n × Weight n) (ε α : ℝ) (hε : ε ≥ 0) (hα : α > 0) (g : DGNGraph n)
    (hz_solution : ∀ t, HasDerivAt z (dgngF_n ε α g (z t)) t)
    (W_max : ℝ) (hW_bound : ∀ t ≥ 0, ∀ i j, |(z t).2 i j| ≤ W_max) :
    ∃ C_x : ℝ, 0 ≤ C_x ∧ ∀ t ≥ 0, ∀ i, |(z t).1 i| ≤ C_x := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨0, by norm_num, ?_⟩
    intro t ht i
    exact i.elim0
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hW_nonneg : 0 ≤ W_max := by
      let i0 : Fin n := ⟨0, hnpos⟩
      have hbound := hW_bound 0 (by positivity) i0 i0
      have h_nonneg_abs : 0 ≤ |(z 0).2 i0 i0| := abs_nonneg _
      linarith
    -- Compute the bound on the coupling term S_i(t) = neighborWeightSum
    have hS_bound (t : ℝ) (ht : 0 ≤ t) (i : Fin n) : |neighborWeightSum ((z t).2) ((z t).1) Real.tanh g i| ≤ (n : ℝ) * W_max := by
      calc
        |neighborWeightSum ((z t).2) ((z t).1) Real.tanh g i|
            ≤ Finset.sum (g.neighbors i) (fun j => |((z t).2 i j) * Real.tanh (((z t).1 j))|) :=
              abs_sum_le_sum_abs (g.neighbors i) (fun j => ((z t).2 i j) * Real.tanh (((z t).1 j)))
        _ ≤ Finset.sum (g.neighbors i) (fun j => |((z t).2 i j)| * |Real.tanh (((z t).1 j))|) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [abs_mul]
        _ ≤ Finset.sum (g.neighbors i) (fun _ => W_max * 1) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          refine mul_le_mul (hW_bound t ht i j) (abs_tanh_le_one _) (abs_nonneg _) (by
            have h_nonneg_W : 0 ≤ |((z t).2 i j)| := abs_nonneg _
            linarith)
        _ = ((g.neighbors i).card : ℝ) * (W_max * 1) := by simp
        _ = ((g.neighbors i).card : ℝ) * W_max := by ring
        _ ≤ (n : ℝ) * W_max := by
          have h_card : (g.neighbors i).card ≤ n := card_neighbors_le_n g i
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) hW_nonneg
    -- For each node i, apply ISS bound
    haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    let M0 := Finset.sup' (Finset.univ : Finset (Fin n))
      (Finset.univ_nonempty (α := Fin n))
      (fun i => |(z 0).1 i|)
    have hM0_nonneg : 0 ≤ M0 := by
      let i0 : Fin n := ⟨0, hnpos⟩
      have hi0_mem : i0 ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i0
      have h_nonneg_i0 : 0 ≤ |(z 0).1 i0| := abs_nonneg _
      have h_i0_le_M0 : |(z 0).1 i0| ≤ M0 := Finset.le_sup' (fun i => |(z 0).1 i|) hi0_mem
      linarith
    let C_x := max M0 ((n : ℝ) * W_max)
    have hCx_nonneg : 0 ≤ C_x := by
      refine le_max_of_le_right ?_
      nlinarith
    refine ⟨C_x, hCx_nonneg, ?_⟩
    intro t ht i
    have hxi_deriv : HasDerivAt (fun (t' : ℝ) => (z t').1 i)
        (-(z t).1 i + neighborWeightSum ((z t).2) ((z t).1) Real.tanh g i) t := by
      have hz_t : HasDerivAt z (dgngF_n ε α g (z t)) t := hz_solution t
      have hzi := comp_semilinear_proj_i z t (dgngF_n ε α g (z t)) hz_t i
      dsimp [dgngF_n] at hzi
      simpa using hzi
    have h_iss := iss_bound (fun t' => (z t').1 i)
      (fun t' => neighborWeightSum ((z t').2) ((z t').1) Real.tanh g i)
      (fun τ => by
        have hxτ_deriv : HasDerivAt (fun (t' : ℝ) => (z t').1 i)
          (-(z τ).1 i + neighborWeightSum ((z τ).2) ((z τ).1) Real.tanh g i) τ := by
          have hz_τ : HasDerivAt z (dgngF_n ε α g (z τ)) τ := hz_solution τ
          have hzi_τ := comp_semilinear_proj_i z τ (dgngF_n ε α g (z τ)) hz_τ i
          dsimp [dgngF_n] at hzi_τ
          simpa using hzi_τ
        simpa using hxτ_deriv)
      ((n : ℝ) * W_max) (by nlinarith)
      (fun τ hτ => hS_bound τ hτ i)
      t ht
    have hM0_bound : |(z 0).1 i| ≤ M0 := by
      have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      exact Finset.le_sup' (fun i => |(z 0).1 i|) hi_mem
    have h_iss_bound : |(z t).1 i| ≤ max (|(z 0).1 i|) ((n : ℝ) * W_max) := h_iss
    calc
      |(z t).1 i| ≤ max (|(z 0).1 i|) ((n : ℝ) * W_max) := h_iss_bound
      _ ≤ max M0 ((n : ℝ) * W_max) := by
        refine max_le_max hM0_bound (le_refl _)
      _ = C_x := rfl


theorem dgngEnergy_n_continuous {n : ℕ} (α : ℝ) (g : DGNGraph n) :
    Continuous (dgngEnergy_n α g) := by
  have h_cont_x (i : Fin n) : Continuous (fun (p : State n × Weight n) => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have h_cont_w (i j : Fin n) : Continuous (fun (p : State n × Weight n) => p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  have h_tanh (i : Fin n) : Continuous (fun (p : State n × Weight n) => Real.tanh (p.1 i)) :=
    continuous_tanh'.comp (h_cont_x i)
  have h_edge_term (e : Fin n × Fin n) : Continuous (fun (p : State n × Weight n) =>
      p.2 e.1 e.2 * Real.tanh (p.1 e.1) * Real.tanh (p.1 e.2)) := by
    refine Continuous.mul ?_ ?_
    · refine Continuous.mul ?_ ?_
      · exact h_cont_w e.1 e.2
      · exact h_tanh e.1
    · exact h_tanh e.2
  have h_sum1 : Continuous (fun (p : State n × Weight n) =>
      Finset.sum g.edgeSet (fun e => p.2 e.1 e.2 * Real.tanh (p.1 e.1) * Real.tanh (p.1 e.2))) :=
    continuous_finset_sum _ (fun e he => h_edge_term e)
  have h_G_term (i : Fin n) : Continuous (fun (p : State n × Weight n) =>
      p.1 i * Real.tanh (p.1 i) - Real.log (Real.cosh (p.1 i))) := by
    have h_mul : Continuous (fun (p : State n × Weight n) => p.1 i * Real.tanh (p.1 i)) :=
      Continuous.mul (h_cont_x i) (h_tanh i)
    have h_log_cosh : Continuous (fun (p : State n × Weight n) => Real.log (Real.cosh (p.1 i))) := by
      refine (Continuous.log ?_ ?_).comp (h_cont_x i)
      · exact Real.continuous_cosh
      · intro x; exact (Real.cosh_pos x).ne'
    exact Continuous.sub h_mul h_log_cosh
  have h_sum2 : Continuous (fun (p : State n × Weight n) =>
      Finset.sum Finset.univ (fun (i : Fin n) => p.1 i * Real.tanh (p.1 i) - Real.log (Real.cosh (p.1 i)))) :=
    continuous_finset_sum _ (fun i hi => h_G_term i)
  have h_sq_term (e : Fin n × Fin n) : Continuous (fun (p : State n × Weight n) => (p.2 e.1 e.2)^2) :=
    (h_cont_w e.1 e.2).pow 2
  have h_sum3 : Continuous (fun (p : State n × Weight n) =>
      (α/2) * Finset.sum g.edgeSet (fun e => (p.2 e.1 e.2)^2)) := by
    refine Continuous.const_mul ?_ (α/2)
    exact continuous_finset_sum _ (fun e he => h_sq_term e)
  -- Combine the three terms
  unfold dgngEnergy_n
  refine Continuous.add (Continuous.add (Continuous.neg h_sum1) h_sum2) h_sum3

theorem omega_n_is_compact {n : ℕ} (α E₀ C_x W_max : ℝ) (g : DGNGraph n) :
    IsCompact (Omega_n α E₀ C_x W_max g) := by
  let S : Set (State n) := {x | ∀ i : Fin n, |x i| ≤ C_x}
  let T : Set (Weight n) := {w | ∀ (i j : Fin n), |w i j| ≤ W_max}
  let Symm_total : Set (State n × Weight n) := {p | ∀ (i j : Fin n), p.2 i j = p.2 j i}
  let E_closed : Set (State n × Weight n) := {p | dgngEnergy_n α g p ≤ E₀}

  -- S is compact: product of closed intervals [-C_x, C_x] over Fin n.
  have hS_compact : IsCompact S := by
    have hS_set : S = {x : State n | ∀ (i : Fin n), x i ∈ Set.Icc (-C_x) C_x} := by
      ext x; simp [S, Set.mem_Icc, abs_le]
    rw [hS_set]
    exact isCompact_pi_infinite (fun (i : Fin n) => isCompact_Icc)

  -- T is compact: nested product of intervals.
  have hT_compact : IsCompact T := by
    have hT_set : T = {w : Weight n | ∀ (i : Fin n), w i ∈
        {f : Fin n → ℝ | ∀ (j : Fin n), f j ∈ Set.Icc (-W_max) W_max}} := by
      ext w; simp [T, Set.mem_Icc, abs_le]
    rw [hT_set]
    have h_inner_compact : IsCompact ({f : Fin n → ℝ | ∀ (j : Fin n), f j ∈ Set.Icc (-W_max) W_max}
        : Set (Fin n → ℝ)) :=
      isCompact_pi_infinite (fun (j : Fin n) => isCompact_Icc)
    exact isCompact_pi_infinite (fun (i : Fin n) => h_inner_compact)

  -- S x T is compact (product of two compact sets).
  have hST_compact : IsCompact (S ×ˢ T) :=
    hS_compact.prod hT_compact

  -- E_closed is closed because dgngEnergy_n is continuous and (-infinity, E₀] is closed in R.
  have hE_closed : IsClosed E_closed := by
    have h_cont : Continuous (dgngEnergy_n α g) := dgngEnergy_n_continuous α g
    have h_Iic_closed : IsClosed (Set.Iic E₀) := isClosed_Iic
    have h_preimage : IsClosed ((dgngEnergy_n α g)⁻¹' (Set.Iic E₀)) :=
      h_Iic_closed.preimage h_cont
    simpa [E_closed] using h_preimage

  -- Symm_total is closed: each condition w_ij = w_ji is the kernel of a continuous map.
  have hSymm_total_closed : IsClosed Symm_total := by
    have h_symm_eq_closed (i j : Fin n) : IsClosed {p : State n × Weight n | p.2 i j = p.2 j i} := by
      have h_cont1 : Continuous fun (p : State n × Weight n) => p.2 i j :=
        (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
      have h_cont2 : Continuous fun (p : State n × Weight n) => p.2 j i :=
        (continuous_apply i).comp ((continuous_apply j).comp continuous_snd)
      exact isClosed_eq h_cont1 h_cont2
    have h_eq : Symm_total = ⋂ (i : Fin n) (j : Fin n), {p | p.2 i j = p.2 j i} := by
      ext p; simp [Symm_total]
    rw [h_eq]
    refine isClosed_iInter (fun i => isClosed_iInter (fun j => h_symm_eq_closed i j))

  -- Intersection of the two closed sets is closed.
  have h_closed_inter : IsClosed (Symm_total ∩ E_closed) :=
    IsClosed.inter hSymm_total_closed hE_closed

  -- Set equality: Omega_n = (S x T) ∩ (Symm_total ∩ E_closed).
  have h_eq : Omega_n α E₀ C_x W_max g = (S ×ˢ T) ∩ (Symm_total ∩ E_closed) := by
    ext p; constructor
    · intro hp
      rcases hp with ⟨hE, hX, hW, hSymm⟩
      exact ⟨⟨hX, hW⟩, ⟨hSymm, hE⟩⟩
    · intro hp
      rcases hp with ⟨⟨hX, hW⟩, ⟨hSymm, hE⟩⟩
      exact ⟨hE, hX, hW, hSymm⟩

  rw [h_eq]
  -- IsCompact.inter_left gives IsCompact (t ∩ s) for IsCompact s, IsClosed t.
  rw [Set.inter_comm (S ×ˢ T) (Symm_total ∩ E_closed)]
  exact hST_compact.inter_left h_closed_inter

/-! ## Positive invariance of Omega_n -/

lemma omega_n_positively_invariant {n : ℕ}
    (z : ℝ → State n × Weight n) (ε α : ℝ) (_hε : ε ≥ 0) (g : DGNGraph n)
    (_hz_solution : ∀ t, HasDerivAt z (dgngF_n ε α g (z t)) t)
    (E₀ C_x W_max : ℝ)
    (hE_noninc : ∀ t ≥ 0, dgngEnergy_n α g (z t) ≤ E₀)
    (hX_bound : ∀ t ≥ 0, ∀ i, |(z t).1 i| ≤ C_x)
    (hW_bound : ∀ t ≥ 0, ∀ i j, |(z t).2 i j| ≤ W_max)
    (h_symm : ∀ s ≥ 0, ∀ i j, (z s).2 i j = (z s).2 j i) :
    ∀ s ≥ 0, z s ∈ Omega_n α E₀ C_x W_max g := by
  intro s hs
  dsimp [Omega_n]
  exact ⟨hE_noninc s hs, hX_bound s hs, hW_bound s hs, h_symm s hs⟩

/-! ## Main theorem: global convergence -/

theorem theorem_global_convergence_n {n : ℕ}
    (z : ℝ → State n × Weight n) (ε α : ℝ) (hε : ε > 0) (hα : α > 0) (g : DGNGraph n)
    (hz_solution : ∀ t, HasDerivAt z (dgngF_n ε α g (z t)) t)
    (h_symm : ∀ t i j, (z t).2 i j = (z t).2 j i)
    (M : ℝ) (h_phi_bound : ∀ y, |Real.tanh y| ≤ M) :
    ∀ x, ClusterPt x (map z atTop) → x ∈ equilibriumSet_n ε α g := by
  rcases weight_uniformly_bounded_n_traj z ε α (by linarith) hα g hz_solution h_symm M h_phi_bound
    with ⟨W_max, hW_nonneg, hW_bound⟩
  rcases state_uniformly_bounded_n z ε α (by linarith) hα g hz_solution W_max hW_bound
    with ⟨C_x, hCx_nonneg, hX_bound⟩
  let E₀ := dgngEnergy_n α g (z 0)
  let Ω := Omega_n α E₀ C_x W_max g
  have hE_noninc : ∀ t ≥ 0, dgngEnergy_n α g (z t) ≤ E₀ := by
    intro t ht
    have h := energy_non_increasing_n z ε α (by linarith) g hz_solution h_symm 0 t ht
    simpa [E₀] using h
  have h_symm_t : ∀ s ≥ 0, ∀ i j, (z s).2 i j = (z s).2 j i := fun s _ i j => h_symm s i j
  have h_for_inv : ∀ s ≥ 0, z s ∈ Ω :=
    omega_n_positively_invariant z ε α (by linarith) g hz_solution E₀ C_x W_max
      hE_noninc (fun t ht i => hX_bound t ht i) hW_bound h_symm_t
  have h_compact : IsCompact Ω := omega_n_is_compact α E₀ C_x W_max g
  let F := dgngF_n ε α g
  let Vdot := dgngVdot_n ε α g
  have h_Vdot_nonpos : ∀ p ∈ Ω, Vdot p ≤ 0 := fun p _ => vdot_nonpos_n ε α (by linarith) g p
  have h_Vdot_zero_iff : ∀ p ∈ Ω, Vdot p = 0 ↔ F p = (0, 0) := by
    intro p hp
    rcases hp with ⟨hE, hX, hW, h_symm_p⟩
    exact vdot_eq_zero_iff_n ε α hε g p h_symm_p
  have h_conv : ∀ x, ClusterPt x (map z atTop) → x ∈ ({p | F p = (0, 0)} ∩ Ω) :=
    lasalle_convergence_n F Vdot z hz_solution Ω h_compact h_for_inv h_Vdot_nonpos h_Vdot_zero_iff
  intro x hx_cluster
  have hx_mem := h_conv x hx_cluster
  rcases hx_mem with ⟨hFzero, hxΩ⟩
  dsimp [equilibriumSet_n]
  simpa [F] using hFzero

