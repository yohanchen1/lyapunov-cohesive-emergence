import Mathlib.Tactic
import DGNG.GraphTheory

/-!
# 定理 3 (n 节点)：δ-内聚划分 — 完整证明

Part A: w*_{ij} = φ_i·φ_j / α
Part B: 符号划分 V⁺/V⁻/V⁰，组内正耦合
Part C: {V⁺, V⁻} 构成 CohesivePartition（V⁰ 分配唯一标签避免成组）
Part D: 自洽方程
-/

open Finset
open DGNGraph

/-! ## Part A #### -/

theorem t3_factorization {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α ≠ 0) (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (i j : Fin n) (h_edge : g.isEdge i j) : w i j = φ (x i) * φ (x j) / α := by
  have h := h_eq i j h_edge
  field_simp [hα] at h ⊢; nlinarith

/-! ## 符号集 & 分组 -/

noncomputable def posSet {n} (x : State n) (φ : ℝ → ℝ) : Finset (Fin n) :=
  filter (fun i => φ (x i) > 0) univ
noncomputable def negSet {n} (x : State n) (φ : ℝ → ℝ) : Finset (Fin n) :=
  filter (fun i => φ (x i) < 0) univ

/-- 分组函数：V⁺→1, V⁻→2, V⁰ 每顶点唯一标签（避免成组） -/
noncomputable def signPart {n} (x : State n) (φ : ℝ → ℝ) : Fin n → ℕ :=
  fun i => if φ (x i) > 0 then 1 else if φ (x i) < 0 then 2 else 3 + i.val

/-! ## Part B -/

theorem t3_pos_coupling {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α > 0) (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (i j : Fin n) (h_edge : g.isEdge i j) (hi : φ (x i) > 0) (hj : φ (x j) > 0) : w i j > 0 := by
  rw [t3_factorization x w φ α g hα.ne' h_eq i j h_edge]
  exact div_pos (mul_pos hi hj) hα

theorem t3_neg_coupling {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α > 0) (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (i j : Fin n) (h_edge : g.isEdge i j) (hi : φ (x i) > 0) (hj : φ (x j) < 0) : w i j < 0 := by
  rw [t3_factorization x w φ α g hα.ne' h_eq i j h_edge]
  have h_mul_neg : φ (x i) * φ (x j) < 0 := by nlinarith
  exact div_neg_iff.mpr (Or.inr ⟨h_mul_neg, hα⟩)

theorem t3_zero_coupling {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α > 0) (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (i j : Fin n) (h_edge : g.isEdge i j) (h_zero : φ (x i) = 0 ∨ φ (x j) = 0) : w i j = 0 := by
  have h := h_eq i j h_edge
  rcases h_zero with (hi | hj)
  · rw [hi] at h; nlinarith
  · rw [hj] at h; nlinarith

/-! ## Part C 核心引理 -/

noncomputable def minAbsPhi {n} (x : State n) (φ : ℝ → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) : ℝ :=
  (S.image (fun i => |φ (x i)|)).min' (Finset.image_nonempty.mpr hS)

lemma minAbsPhi_le {n} (x : State n) (φ : ℝ → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) (i : Fin n)
    (hi : i ∈ S) : minAbsPhi x φ S hS ≤ |φ (x i)| := by
  unfold minAbsPhi
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-! ## Part C 主定理 -/

noncomputable def theorem3_cohesive_partition_n {n : ℕ}
    (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α > 0) (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (hVp : (posSet x φ).Nonempty) (hVn : (negSet x φ).Nonempty) :
    CohesivePartition n g w := by
  let P := signPart x φ
  let Vp := posSet x φ
  let Vn := negSet x φ
  let mVp := minAbsPhi x φ (posSet x φ) hVp
  let mVn := minAbsPhi x φ (negSet x φ) hVn
  let m := min mVp mVn
  let θ_h := m ^ 2 / α
  -- m > 0 因为 V⁺ 中有正 φ，V⁻ 中有负 φ
  have hmVp_pos : mVp > 0 := by
    dsimp [mVp, minAbsPhi]
    have hmem := Finset.min'_mem ((posSet x φ).image (fun i => |φ (x i)|))
      (Finset.image_nonempty.mpr hVp)
    rcases Finset.mem_image.mp hmem with ⟨k, hk, h_eq⟩
    have hk_pos : φ (x k) > 0 := by
      rcases Finset.mem_filter.mp hk with ⟨_, h⟩; exact h
    have h_abs_pos : |φ (x k)| > 0 := abs_pos.mpr hk_pos.ne'
    simpa [h_eq] using h_abs_pos
  have hmVn_pos : mVn > 0 := by
    dsimp [mVn, minAbsPhi]
    have hmem := Finset.min'_mem ((negSet x φ).image (fun i => |φ (x i)|))
      (Finset.image_nonempty.mpr hVn)
    rcases Finset.mem_image.mp hmem with ⟨k, hk, h_eq⟩
    have hk_neg : φ (x k) < 0 := by
      rcases Finset.mem_filter.mp hk with ⟨_, h⟩; exact h
    have h_abs_pos : |φ (x k)| > 0 := abs_pos.mpr hk_neg.ne
    simpa [h_eq] using h_abs_pos
  have hm_pos : m > 0 :=
    lt_min_iff.mpr ⟨hmVp_pos, hmVn_pos⟩
  have h_θ_pos : θ_h > 0 := div_pos (pow_pos hm_pos 2) hα
  -- 同组→同号引理：P(i)=P(j) 且 i≠j → 两者同号
  have h_same_sign : ∀ i j, i ≠ j → P i = P j →
      (φ (x i) > 0 ∧ φ (x j) > 0) ∨ (φ (x i) < 0 ∧ φ (x j) < 0) := by
    intro i j h_ne h_eqP
    dsimp [P, signPart] at h_eqP
    by_cases hi_pos : φ (x i) > 0
    · simp [hi_pos] at h_eqP
      -- h_eqP: 1 = (if φ(x_j)>0 then 1 else if φ(x_j)<0 then 2 else 3+j.val)
      by_cases hj_pos : φ (x j) > 0
      · exact Or.inl ⟨hi_pos, hj_pos⟩
      · by_cases hj_neg : φ (x j) < 0
        · simp [hj_pos, hj_neg] at h_eqP
        · have hj_zero : φ (x j) = 0 := by linarith
          simp [hj_zero] at h_eqP
          omega
    · by_cases hi_neg : φ (x i) < 0
      · simp [hi_pos, hi_neg] at h_eqP
        -- h_eqP: 2 = (if φ(x_j)>0 then 1 else if φ(x_j)<0 then 2 else 3+j.val)
        by_cases hj_pos : φ (x j) > 0
        · simp [hj_pos] at h_eqP
        · by_cases hj_neg : φ (x j) < 0
          · exact Or.inr ⟨hi_neg, hj_neg⟩
          · have hj_zero : φ (x j) = 0 := by linarith
            simp [hj_zero] at h_eqP
            omega
      · -- φ(x_i) = 0 → P(i) = 3 + i.val, need P(j) = P(i) also
        have hi_zero : φ (x i) = 0 := by linarith
        simp [hi_pos, hi_neg] at h_eqP
        -- h_eqP: 3 + i.val = (if φ(x_j)>0 then 1 else if φ(x_j)<0 then 2 else 3+j.val)
        by_cases hj_pos : φ (x j) > 0
        · simp [hj_pos] at h_eqP; omega
        · by_cases hj_neg : φ (x j) < 0
          · simp [hj_pos, hj_neg] at h_eqP; omega
          · have hj_zero : φ (x j) = 0 := by linarith
            simp [hj_zero] at h_eqP
            -- h_eqP: 3 + i.val = 3 + j.val
            have h_val_eq : i.val = j.val := by omega
            have h_eq : i = j := Fin.ext h_val_eq
            exact absurd h_eq h_ne
  -- 异组→符号相反/含零
  have h_diff_sign : ∀ i j, P i ≠ P j → φ (x i) * φ (x j) ≤ 0 := by
    intro i j h_diff
    by_cases hi_pos : φ (x i) > 0
    · by_cases hj_pos : φ (x j) > 0
      · -- both >0 → P(i)=P(j)=1, contradiction
        have hPi : P i = 1 := by dsimp [P, signPart]; simp [hi_pos]
        have hPj : P j = 1 := by dsimp [P, signPart]; simp [hj_pos]
        rw [hPi, hPj] at h_diff
        exact absurd rfl h_diff
      · by_cases hj_neg : φ (x j) < 0
        · -- i>0, j<0 → product < 0
          have : φ (x i) * φ (x j) < 0 := by nlinarith
          linarith
        · -- i>0, j=0 → product = 0
          have h_zero : φ (x j) = 0 := by linarith
          simp [h_zero]
    · by_cases hi_neg : φ (x i) < 0
      · by_cases hj_pos : φ (x j) > 0
        · -- i<0, j>0 → product < 0
          have : φ (x i) * φ (x j) < 0 := by nlinarith
          linarith
        · by_cases hj_neg : φ (x j) < 0
          · -- both <0 → P(i)=P(j)=2, contradiction
            have hPi : P i = 2 := by dsimp [P, signPart]; simp [hi_pos, hi_neg]
            have hPj : P j = 2 := by dsimp [P, signPart]; simp [hj_pos, hj_neg]
            rw [hPi, hPj] at h_diff
            exact absurd rfl h_diff
          · -- i<0, j=0 → product = 0
            have h_zero : φ (x j) = 0 := by linarith
            simp [h_zero]
      · -- i=0 → product = 0 regardless of j
        have h_zero : φ (x i) = 0 := by linarith
        simp [h_zero]
  -- 构造 CohesivePartition 的各个字段
  have h_delta_proof : θ_h - 0 ≥ θ_h := by nlinarith
  have h_intra_proof : ∀ i j, g.isEdge i j → P i = P j → w i j ≥ θ_h := by
    intro i j h_edge h_sameP
    have h_ne : i ≠ j := by
      intro h_eq; subst h_eq; exact isEdge_irreflexive g i h_edge
    have h_factor : w i j = φ (x i) * φ (x j) / α :=
      t3_factorization x w φ α g hα.ne' h_eq i j h_edge
    rw [h_factor]
    rcases h_same_sign i j h_ne h_sameP with (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · -- Both > 0
      have hi_ge : mVp ≤ φ (x i) := by
        dsimp [mVp]
        have hmem : i ∈ posSet x φ := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hthis := minAbsPhi_le x φ (posSet x φ) hVp i hmem
        rw [abs_of_pos hi] at hthis; exact hthis
      have hj_ge : mVp ≤ φ (x j) := by
        dsimp [mVp]
        have hmem : j ∈ posSet x φ := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        have hthis := minAbsPhi_le x φ (posSet x φ) hVp j hmem
        rw [abs_of_pos hj] at hthis; exact hthis
      have hm_le_phi_i : m ≤ φ (x i) := le_trans (min_le_left _ _) hi_ge
      have hm_le_phi_j : m ≤ φ (x j) := le_trans (min_le_left _ _) hj_ge
      have h_prod : m^2 ≤ φ (x i) * φ (x j) := by nlinarith
      have : φ (x i) * φ (x j) / α - m^2 / α = (φ (x i) * φ (x j) - m^2) / α := by ring
      have h_nonneg : 0 ≤ (φ (x i) * φ (x j) - m^2) / α :=
        div_nonneg (by nlinarith) (by linarith)
      linarith
    · -- Both < 0
      have hi_abs_ge : mVn ≤ -φ (x i) := by
        dsimp [mVn]
        have hmem : i ∈ negSet x φ := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hthis := minAbsPhi_le x φ (negSet x φ) hVn i hmem
        rw [abs_of_neg hi] at hthis; exact hthis
      have hj_abs_ge : mVn ≤ -φ (x j) := by
        dsimp [mVn]
        have hmem : j ∈ negSet x φ := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        have hthis := minAbsPhi_le x φ (negSet x φ) hVn j hmem
        rw [abs_of_neg hj] at hthis; exact hthis
      have hm_le_abs_i : m ≤ -φ (x i) := le_trans (min_le_right _ _) hi_abs_ge
      have hm_le_abs_j : m ≤ -φ (x j) := le_trans (min_le_right _ _) hj_abs_ge
      have h_prod : m^2 ≤ φ (x i) * φ (x j) := by
        have : φ (x i) * φ (x j) = (-φ (x i)) * (-φ (x j)) := by ring
        rw [this]; nlinarith
      have : φ (x i) * φ (x j) / α - m^2 / α = (φ (x i) * φ (x j) - m^2) / α := by ring
      have h_nonneg : 0 ≤ (φ (x i) * φ (x j) - m^2) / α :=
        div_nonneg (by nlinarith) (by linarith)
      linarith
  have h_inter_proof : ∀ i j, g.isEdge i j → P i ≠ P j → w i j ≤ 0 := by
    intro i j h_edge h_diffP
    have h_factor : w i j = φ (x i) * φ (x j) / α :=
      t3_factorization x w φ α g hα.ne' h_eq i j h_edge
    rw [h_factor]
    have h_prod_nonpos : φ (x i) * φ (x j) ≤ 0 := h_diff_sign i j h_diffP
    exact div_nonpos_of_nonpos_of_nonneg h_prod_nonpos (by linarith)
  exact CohesivePartition.mk P θ_h 0 θ_h h_θ_pos h_delta_proof h_θ_pos h_intra_proof h_inter_proof

/-! ## Part D：自洽方程 -/

noncomputable def hFunc (φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s = 0 then 1 else s / φ s

/-- j 是 i 的邻居 → (i,j) 是无向边 -/
lemma mem_neighbors_imp_isEdge {n} (g : DGNGraph n) (i j : Fin n) (h : j ∈ g.neighbors i) : g.isEdge i j := by
  unfold neighbors at h
  -- h: j ∈ (directedEdges.filter (λ⟨a,_⟩→ a=i)).image Prod.snd
  rcases Finset.mem_image.mp h with ⟨⟨a, b⟩, hmem, rfl⟩
  -- hmem: (a,b) ∈ directedEdges.filter (λ⟨a',_⟩→ a'=i)
  -- rfl: Prod.snd (a,b) = j → b 被替换为 j（目标中 j 变为 b）
  rcases Finset.mem_filter.mp hmem with ⟨hmem_dir, ha_eq_i⟩
  -- hmem_dir: (a,b) ∈ directedEdges, ha_eq_i: a = i
  subst ha_eq_i
  -- 目标: g.isEdge i b，即 (i,b) ∈ directedEdges
  unfold isEdge
  exact hmem_dir

theorem t3_self_consistency {n} (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α ≠ 0) (h_eq_w : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (h_eq_x : ∀ i, x i = neighborWeightSum w x φ g i)
    (i : Fin n) : x i = (1/α) * φ (x i) * (Finset.sum (g.neighbors i) (fun j => (φ (x j))^2)) := by
  calc
    x i = neighborWeightSum w x φ g i := by rw [h_eq_x i]
    _ = Finset.sum (g.neighbors i) (fun j => w i j * φ (x j)) := rfl
    _ = Finset.sum (g.neighbors i) (fun j => ((1/α) * φ (x i) * φ (x j)) * φ (x j)) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have h_edge : g.isEdge i j := mem_neighbors_imp_isEdge g i j hj
      rw [t3_factorization x w φ α g hα h_eq_w i j h_edge]
      ring
    _ = Finset.sum (g.neighbors i) (fun j => (1/α) * φ (x i) * ((φ (x j))^2)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    _ = (1/α) * φ (x i) * (Finset.sum (g.neighbors i) (fun j => (φ (x j))^2)) := by
      simp [Finset.mul_sum]
