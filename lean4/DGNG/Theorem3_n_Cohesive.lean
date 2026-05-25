import Mathlib.Tactic
import DGNG.GraphTheory

/-!
# 定理 3 Part C：δ-内聚划分的 n 节点构造

从符号划分 V⁺/V⁻/V⁰ 出发，构造 CohesivePartition。
θ_high = min_{i∈V⁺∪V⁻} φ(x_i)² / α > 0, θ_low = 0。
-/

open Finset
open DGNGraph

/-- Part A: 权重因子化 -/
theorem t3_factorization_n {n : ℕ}
    (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n) (hα : α ≠ 0)
    (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (i j : Fin n) (h_edge : g.isEdge i j) : w i j = (1/α) * φ (x i) * φ (x j) := by
  have h := h_eq i j h_edge
  field_simp [hα] at h ⊢
  nlinarith

/-- 符号集 -/
noncomputable def pos_set {n} (x : State n) (φ : ℝ → ℝ) : Finset (Fin n) :=
  filter (fun i => φ (x i) > 0) univ
noncomputable def neg_set {n} (x : State n) (φ : ℝ → ℝ) : Finset (Fin n) :=
  filter (fun i => φ (x i) < 0) univ
noncomputable def zero_set {n} (x : State n) (φ : ℝ → ℝ) : Finset (Fin n) :=
  filter (fun i => φ (x i) = 0) univ
noncomputable def signPartition {n} (x : State n) (φ : ℝ → ℝ) : Fin n → ℕ :=
  fun i => if φ (x i) > 0 then 1 else if φ (x i) < 0 then 2 else 0

/-! ## Part C 证明：核心引理

我们需要定义 θ_high = min( min_{i∈V⁺} φ(x_i)², min_{i∈V⁻} φ(x_i)² ) / α。

由于 φ 奇函数，|φ(x_i)|² = φ(x_i)²，V⁺/V⁻ 的 φ² 最小值可以统一处理。

关键步骤：
1. 取 φ² 在 V⁺∪V⁻ 上的最小值 → 最小 φ² 所在顶点 r
2. 定义 θ_high = φ(x_r)² / α > 0
3. 对所有同组边 (i,j)：φ(x_i)·φ(x_j) = |φ(x_i)|·|φ(x_j)| ≥ φ(x_r)²
4. 故 w_ij = φ_i·φ_j/α ≥ θ_high
5. 对所有异组边 (i,j)：φ(x_i)·φ(x_j) < 0 → w_ij < 0 = θ_low
-/

/-- 从 nonempty finset 中取 φ² 最小的顶点 -/
noncomputable def min_phi_sq_vertex {n} (x : State n) (φ : ℝ → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) : Fin n :=
  S.min' hS

/-- θ_high：取 V⁺ 和 V⁻ 中最小的 φ²，除以 α -/
noncomputable def compute_theta_high {n} (x : State n) (φ : ℝ → ℝ) (α : ℝ)
    (hVp : (pos_set x φ).Nonempty) (hVn : (neg_set x φ).Nonempty) : ℝ :=
  let Vp := pos_set x φ
  let Vn := neg_set x φ
  let ap := Vp.min' hVp
  let an := Vn.min' hVn
  let sqVp := (φ (x ap)) ^ 2
  let sqVn := (φ (x an)) ^ 2
  min sqVp sqVn / α

/-!
## 主定理：符号划分构成 δ-内聚划分
-/

theorem theorem3_cohesive_partition_n {n : ℕ}
    (x : State n) (w : Weight n) (φ : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (hα : α > 0) (h_eq : ∀ i j, g.isEdge i j → α * w i j = φ (x i) * φ (x j))
    (hVp_nonempty : (pos_set x φ).Nonempty) (hVn_nonempty : (neg_set x φ).Nonempty) :
    CohesivePartition n g w := by
  let Vp := pos_set x φ
  let Vn := neg_set x φ
  let P := signPartition x φ
  -- 构造 Vp∪Vn 上 φ² 值的 Finset，然后取 min'
  let sq_vals : Finset ℝ := (Vp.image (fun i => φ (x i) ^ 2)) ∪ (Vn.image (fun i => φ (x i) ^ 2))
  have h_sq_nonempty : sq_vals.Nonempty := by
    rcases hVp_nonempty with ⟨i, hi⟩
    refine ⟨φ (x i) ^ 2, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
  let m_sq := sq_vals.min' h_sq_nonempty
  have hm_sq_pos : m_sq > 0 := by
    have hmem : m_sq ∈ sq_vals := Finset.min'_mem _ _ h_sq_nonempty
    rcases Finset.mem_union.mp hmem with (hy' | hy')
    · rcases Finset.mem_image.mp hy' with ⟨i, hi, rfl⟩
      have hi_pos : φ (x i) > 0 := by
        rcases Finset.mem_filter.mp hi with ⟨_, h⟩; exact h
      exact pow_pos hi_pos 2
    · rcases Finset.mem_image.mp hy' with ⟨i, hi, rfl⟩
      have hi_neg : φ (x i) < 0 := by
        rcases Finset.mem_filter.mp hi with ⟨_, h⟩; exact h
      exact pow_pos (by linarith) 2
  -- θ_high = m_sq / α
  let θ_h := m_sq / α
  have h_θ_pos : θ_h > 0 := div_pos hm_sq_pos hα
  -- 核心引理：对任意 i ∈ Vp ∪ Vn，φ(x_i)² ≥ m_sq
  have h_sq_min : ∀ i, i ∈ Vp → m_sq ≤ φ (x i) ^ 2 := by
    intro i hi
    have hmem : φ (x i) ^ 2 ∈ sq_vals :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    exact Finset.min'_le _ _ hmem
  have h_sq_min' : ∀ i, i ∈ Vn → m_sq ≤ φ (x i) ^ 2 := by
    intro i hi
    have hmem : φ (x i) ^ 2 ∈ sq_vals :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    exact Finset.min'_le _ _ hmem
  -- 同组→乘积 ≥ m_sq 的引理
  have h_prod_ge_m_sq : ∀ i j, (i ∈ Vp ∧ j ∈ Vp) ∨ (i ∈ Vn ∧ j ∈ Vn) → m_sq ≤ φ (x i) * φ (x j) := by
    intro i j h_cases
    rcases h_cases with (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · have hpos_i : φ (x i) > 0 := by
        rcases Finset.mem_filter.mp hi with ⟨_, h⟩; exact h
      have hpos_j : φ (x j) > 0 := by
        rcases Finset.mem_filter.mp hj with ⟨_, h⟩; exact h
      have h_sq_i : m_sq ≤ φ (x i) ^ 2 := h_sq_min i hi
      have h_sq_j : m_sq ≤ φ (x j) ^ 2 := h_sq_min j hj
      -- (φ_i·φ_j)² = φ_i²·φ_j² ≥ m_sq² → φ_i·φ_j - m_sq ≥ 0（因 φ_i·φ_j>0）
      have h_sq_prod : (φ (x i) * φ (x j)) ^ 2 ≥ m_sq ^ 2 := by
        nlinarith
      have h_prod_pos : φ (x i) * φ (x j) > 0 := mul_pos hpos_i hpos_j
      -- (φi·φj - m) (φi·φj + m) ≥ 0, 且 φi·φj+m > 0 → φi·φj - m ≥ 0
      have h_factor : (φ (x i) * φ (x j) - m_sq) * (φ (x i) * φ (x j) + m_sq) ≥ 0 := by
        nlinarith
      have h_sum_pos : φ (x i) * φ (x j) + m_sq > 0 := by linarith
      nlinarith
    · have hneg_i : φ (x i) < 0 := by
        rcases Finset.mem_filter.mp hi with ⟨_, h⟩; exact h
      have hneg_j : φ (x j) < 0 := by
        rcases Finset.mem_filter.mp hj with ⟨_, h⟩; exact h
      have h_sq_i : m_sq ≤ φ (x i) ^ 2 := h_sq_min' i hi
      have h_sq_j : m_sq ≤ φ (x j) ^ 2 := h_sq_min' j hj
      -- φ_i·φ_j = (-φ_i)·(-φ_j) > 0，同样方法
      have h_sq_prod : (φ (x i) * φ (x j)) ^ 2 ≥ m_sq ^ 2 := by
        nlinarith
      have h_prod_pos : φ (x i) * φ (x j) > 0 := by nlinarith
      have h_factor : (φ (x i) * φ (x j) - m_sq) * (φ (x i) * φ (x j) + m_sq) ≥ 0 := by
        nlinarith
      have h_sum_pos : φ (x i) * φ (x j) + m_sq > 0 := by linarith
      nlinarith
  -- 异组→乘积 ≤ 0 的引理
  have h_sign_cases : ∀ i, P i = 1 ↔ φ (x i) > 0 := by
    intro i; unfold P signPartition; constructor <;> intro h
    · by_contra! H; simp [H] at h
    · simp [h]
  have h_sign_cases' : ∀ i, P i = 2 ↔ φ (x i) < 0 := by
    intro i; unfold P signPartition; constructor <;> intro h
    · by_contra! H
      by_cases hpos : φ (x i) > 0
      · simp [hpos] at h
      · simp [hpos, H] at h
    · simp [h]
  have h_sign_cases0 : ∀ i, P i = 0 ↔ φ (x i) = 0 := by
    intro i; unfold P signPartition; constructor <;> intro h
    · by_contra! H
      by_cases hpos : φ (x i) > 0
      · simp [hpos] at h
      · by_cases hneg : φ (x i) < 0
        · simp [hpos, hneg] at h
        · linarith
    · simp [h]
  refine {
    partition := P
    θ_high := θ_h
    θ_low := 0
    δ := θ_h
    h_theta_high_pos := h_θ_pos
    h_delta := by
      dsimp [θ_high, θ_low, δ]
      nlinarith
    h_delta_pos := h_θ_pos
    h_intra := ?
    h_inter := ?
  }
  · -- 同组内聚：P(i)=P(j) → w_ij ≥ θ_high
    intro i j h_edge h_sameP
    have h_factor : w i j = φ (x i) * φ (x j) / α := by
      have h := t3_factorization_n x w φ α g hα.ne' h_eq i j h_edge
      rw [h]; ring
    rw [h_factor]
    -- 需要判断 P(i)=P(j) 的具体值（1 或 2）
    by_cases h_one : P i = 1
    · -- P(i) = P(j) = 1 → i,j ∈ Vp
      have hi_Vp : i ∈ Vp := by
        rw [h_sign_cases i] at h_one
        apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ i, h_one⟩
      have hj_Vp : j ∈ Vp := by
        rw [h_sameP] at h_one
        rw [h_sign_cases j] at h_one
        apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ j, h_one⟩
      have h_prod : m_sq ≤ φ (x i) * φ (x j) :=
        h_prod_ge_m_sq i j (Or.inl ⟨hi_Vp, hj_Vp⟩)
      exact (div_le_div_right hα).mpr h_prod
    · -- P(i) ≠ 1，则必然 P(i) = 2（因 P≠0，否则 i=j 且 V⁰，但 h_edge 排除自环）
      have hi_Vn : i ∈ Vn := by
        have h_cases_i : φ (x i) < 0 := by
          by_contra! H
          have h_zero : P i = 0 := by
            unfold P signPartition; simp [H]
          rw [h_zero] at h_one
          exact h_one rfl
        apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ i, h_cases_i⟩
      have hj_Vn : j ∈ Vn := by
        have hPj : P j = 2 := by
          rw [h_sameP]
          by_contra! H
          have h_zero : P i = 0 := by
            unfold P signPartition
            by_cases hpos : φ (x i) > 0
            · simp [hpos]
            · by_cases hneg : φ (x i) < 0
              · simp [hpos, hneg] at H; exact H
              · simp [hpos, hneg]
          rw [h_zero] at h_one
          exact h_one rfl
        have h_cases_j : φ (x j) < 0 := by
          rw [h_sign_cases' j] at hPj; exact hPj
        apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ j, h_cases_j⟩
      have h_prod : m_sq ≤ φ (x i) * φ (x j) :=
        h_prod_ge_m_sq i j (Or.inr ⟨hi_Vn, hj_Vn⟩)
      exact (div_le_div_right hα).mpr h_prod
  · -- 异组分离：P(i)≠P(j) → w_ij ≤ 0 = θ_low
    intro i j h_edge h_diffP
    have h_factor : w i j = φ (x i) * φ (x j) / α := by
      have h := t3_factorization_n x w φ α g hα.ne' h_eq i j h_edge
      rw [h]; ring
    rw [h_factor]
    -- P(i)≠P(j)：检查各种组合，证明 φ_i·φ_j ≤ 0
    by_cases hi_pos : φ (x i) > 0
    · -- i>0: P(i)=1。若 P(j)=1 则矛盾（P(i)=P(j)），故 P(j)∈{0,2}
      -- P(j)=0 → φ_j=0 → 乘积=0; P(j)=2 → φ_j<0 → 乘积<0
      by_cases hj_pos : φ (x j) > 0
      · -- 两者都>0 → P相同，矛盾
        have : P i = P j := by
          unfold P signPartition; simp [hi_pos, hj_pos]
        exact absurd this h_diffP
      · by_cases hj_neg : φ (x j) < 0
        · -- i>0, j<0 → 乘积<0
          have h_neg_prod : φ (x i) * φ (x j) < 0 := by nlinarith
          have : φ (x i) * φ (x j) / α ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          exact this
        · -- j=0 → 乘积=0
          simp [hj_pos, hj_neg]
    · by_cases hi_neg : φ (x i) < 0
      · -- i<0: P(i)=2
        by_cases hj_pos : φ (x j) > 0
        · have h_neg_prod : φ (x i) * φ (x j) < 0 := by nlinarith
          have : φ (x i) * φ (x j) / α ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          exact this
        · by_cases hj_neg : φ (x j) < 0
          · -- 两者都<0 → P相同=2 → 矛盾
            have : P i = P j := by
              unfold P signPartition; simp [hi_pos, hi_neg, hj_pos, hj_neg]
            exact absurd this h_diffP
          · -- j=0 → 乘积=0
            simp [hj_pos, hj_neg]
      · -- i=0: P(i)=0，乘积=0
        simp [hi_pos, hi_neg]
