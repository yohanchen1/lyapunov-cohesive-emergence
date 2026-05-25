import Mathlib.Tactic
import DGNG.GraphTheory
import DGNG.Theorem1_n
import DGNG.Theorem2

/-!
# 定理 2 (n 节点)：能量下界

本文件导入 Theorem1_n.lean 中的 `lyapunov_E`（已修正，无 1/2 因子，与 Paper 一致）。

对于 G(φ(x_i)) ≥ 0 和 |φ(x_i)| ≤ M：
  E ≥ (α/4)·Σ w_ij² - m·M⁴/α

证明：由 (α/2·w - ab)² ≥ 0 展开，得 -w·ab + (α/2)·w² ≥ (α/4)·w² - (ab)²/α。
再用 |ab| ≤ M² 得到最终下界。
-/

open Finset
open DGNGraph

/-! ### 辅助引理：ab ≤ (t/2)a² + (1/(2t))b² （t > 0）

由 (t·a - b)² ≥ 0 展开后两边除以 2t 即得。
注意全程只用 `ring`/`linarith`/`field_simp`，不使用 `nlinarith` 以避免除法类型问题。
-/

lemma am_gm_bound (a b t : ℝ) (ht : t > 0) : a * b ≤ (t/2) * a^2 + (1/(2*t)) * b^2 := by
  have h_sq_nonneg : (t*a - b)^2 ≥ 0 := sq_nonneg _
  have h_identity : a * b = (t/2)*a^2 + (1/(2*t))*b^2 - ((t*a - b)^2)/(2*t) := by
    field_simp [ht.ne']
    ring
  have h_div_nonneg : 0 ≤ ((t*a - b)^2)/(2*t) := by
    refine div_nonneg (sq_nonneg _) (by positivity)
  rw [h_identity]
  linarith

/-! ### |a| ≤ M, |b| ≤ M ⟹ (a·b)² ≤ M⁴ -/

lemma sq_prod_le_M4 (a b M : ℝ) (ha : |a| ≤ M) (hb : |b| ≤ M) : (a * b)^2 ≤ M^4 := by
  have hM : 0 ≤ M := by
    have h_nonneg_a : 0 ≤ |a| := abs_nonneg _
    linarith
  have h_abs_bound : |a * b| ≤ M^2 := by
    calc
      |a * b| = |a| * |b| := abs_mul a b
      _ ≤ M * M := mul_le_mul ha hb (abs_nonneg _) hM
      _ = M^2 := by ring
  have h_sq_eq : (a * b)^2 = (|a * b|)^2 := by simpa using (sq_abs (a * b)).symm
  rw [h_sq_eq]
  have h_nonneg_abs : 0 ≤ |a * b| := abs_nonneg _
  have h_sq_bound : (|a * b|)^2 ≤ (M^2)^2 := by nlinarith
  calc
    (|a * b|)^2 ≤ (M^2)^2 := h_sq_bound
    _ = M^4 := by ring

/-! ## 定理 2 n 节点：能量下界 -/

theorem energy_lower_bound_n {n : ℕ}
    (x : State n) (w : Weight n) (φ G : ℝ → ℝ) (α : ℝ) (g : DGNGraph n)
    (M : ℝ) (hα : α > 0)
    (h_G_nonneg : ∀ i, G (φ (x i)) ≥ 0)
    (h_phi_bound : ∀ i, |φ (x i)| ≤ M) :
    lyapunov_E x w φ G α g ≥ (α/4) * Finset.sum g.edgeSet (fun p => (w p.1 p.2)^2)
                          - (g.edgeCount : ℝ) * (M^4) / α := by
  -- Per-edge bound: -w·ab + (α/2)·w² ≥ (α/4)·w² - M⁴/α
  -- Proof: (α/2·w - ab)² ≥ 0 → a·b ≤ (α/4)·a² + (1/α)·b² via am_gm_bound with t=α/2
  have h_edge : ∀ p ∈ g.edgeSet,
      -(w p.1 p.2) * φ (x p.1) * φ (x p.2) + (α/2) * (w p.1 p.2)^2
      ≥ (α/4) * (w p.1 p.2)^2 - M^4 / α := by
    intro p hp
    let a := w p.1 p.2
    let b := φ (x p.1) * φ (x p.2)
    have hα2 : α/2 > 0 := by nlinarith
    have hab : a * b ≤ (α/4) * a^2 + (1/α) * b^2 := by
      have htemp := am_gm_bound a b (α/2) hα2
      have h_simp : ((α / 2) / 2 : ℝ) * a ^ 2 + ((1 : ℝ) / (2 * (α / 2))) * b ^ 2
                  = (α/4) * a^2 + (1/α) * b^2 := by ring
      rw [h_simp] at htemp
      exact htemp
    have h_sq : b^2 ≤ M^4 := sq_prod_le_M4 (φ (x p.1)) (φ (x p.2)) M
      (h_phi_bound p.1) (h_phi_bound p.2)
    have h_step1 : -a * b ≥ -(α/4) * a^2 - (1/α) * b^2 := by linarith
    have h_step2 : -a * b + (α/2) * a^2 ≥ (α/4) * a^2 - (1/α) * b^2 := by linarith
    have h_step3 : (α/4) * a^2 - (1/α) * b^2 ≥ (α/4) * a^2 - M^4/α := by
      have h_term : (1/α) * b^2 ≤ M^4/α := by
        calc
          (1/α) * b^2 = b^2 * (1/α) := by ring
          _ ≤ M^4 * (1/α) := mul_le_mul_of_nonneg_right h_sq (by positivity)
          _ = M^4/α := by ring
      linarith
    linarith
  -- Expand lyapunov_E into per-edge sums + G sum
  unfold lyapunov_E
  calc
    -Finset.sum g.edgeSet (fun p => w p.1 p.2 * φ (x p.1) * φ (x p.2))
    + (Finset.sum Finset.univ (fun (i : Fin n) => G (φ (x i))))
    + (α/2) * (Finset.sum g.edgeSet fun p => (w p.1 p.2)^2)
    = (Finset.sum g.edgeSet fun p =>
        (-(w p.1 p.2) * φ (x p.1) * φ (x p.2) + (α/2) * (w p.1 p.2)^2))
      + (Finset.sum Finset.univ fun (i : Fin n) => G (φ (x i))) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≥ (Finset.sum g.edgeSet fun p =>
        (-(w p.1 p.2) * φ (x p.1) * φ (x p.2) + (α/2) * (w p.1 p.2)^2)) := by
      have h_sum_nonneg : 0 ≤ Finset.sum Finset.univ (fun (i : Fin n) => G (φ (x i))) :=
        Finset.sum_nonneg (fun i _ => h_G_nonneg i)
      linarith
    _ ≥ (Finset.sum g.edgeSet fun p => (α/4) * (w p.1 p.2)^2 - M^4 / α) :=
      Finset.sum_le_sum h_edge
    _ = (α/4) * (Finset.sum g.edgeSet fun p => (w p.1 p.2)^2)
        - ((Finset.card g.edgeSet : ℝ) * M^4 / α) := by
      simp [Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    _ = (α/4) * (Finset.sum g.edgeSet fun p => (w p.1 p.2)^2)
        - (g.edgeCount : ℝ) * (M^4) / α := rfl

/-! ## 推论：权重一致有界 -/

theorem weight_uniformly_bounded_n {n : ℕ}
    (x0 : State n) (w0 : Weight n) (φ G : ℝ → ℝ) (α : ℝ) (g : DGNGraph n) (M : ℝ)
    (hα : α > 0) (h_G_nonneg : ∀ y, G y ≥ 0)
    (h_phi_bound : ∀ y, |φ y| ≤ M) :
    ∃ C_w : ℝ, ∀ (t : ℝ), t ≥ 0 → ∀ (x_t : State n) (w_t : Weight n),
      (lyapunov_E x_t w_t φ G α g ≤ lyapunov_E x0 w0 φ G α g) →
      Finset.sum g.edgeSet (fun p => (w_t p.1 p.2)^2) ≤ C_w := by
  let E0 := lyapunov_E x0 w0 φ G α g
  -- From E ≥ (α/4)·Σw² - m·M⁴/α and E ≤ E0:
  -- Σ w_ij² ≤ (4/α)·E0 + 4·m·M⁴/α²
  let C_w := (4/α)*E0 + 4*(g.edgeCount : ℝ)*M^4/(α^2)
  refine ⟨C_w, ?_⟩
  intro t ht x_t w_t hE
  have h_bound := energy_lower_bound_n x_t w_t φ G α g M hα
    (fun i => h_G_nonneg (φ (x_t i))) (fun i => h_phi_bound (x_t i))
  have hE_t : lyapunov_E x_t w_t φ G α g ≤ E0 := hE
  have h_chain : (α/4) * Finset.sum g.edgeSet (fun p => (w_t p.1 p.2)^2)
               - (g.edgeCount : ℝ) * (M^4) / α ≤ E0 := by
    linarith
  have h_result : Finset.sum g.edgeSet (fun p => (w_t p.1 p.2)^2) ≤ C_w := by
    have h_mul : (α/4) * Finset.sum g.edgeSet (fun p => (w_t p.1 p.2)^2)
                ≤ E0 + (g.edgeCount : ℝ) * (M^4) / α := by
      linarith
    calc
      Finset.sum g.edgeSet (fun p => (w_t p.1 p.2)^2)
          = ((4/α) : ℝ) * ((α/4) * Finset.sum g.edgeSet (fun p => (w_t p.1 p.2)^2)) := by
            field_simp [hα.ne']
      _ ≤ ((4/α) : ℝ) * (E0 + (g.edgeCount : ℝ) * (M^4) / α) := by
        refine mul_le_mul_of_nonneg_left h_mul ?_
        positivity
      _ = C_w := by
        dsimp [C_w]
        field_simp [hα.ne']
  exact h_result
