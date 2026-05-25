import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-!
# 图论基础设施：稀疏无向图 + δ-内聚划分

顶点 = `Fin n`，每条无向边在 `edgeSet` 中只存一次（i < j）。
-/

open Finset
open scoped BigOperators

structure DGNGraph (n : ℕ) where
  edgeSet : Finset (Fin n × Fin n)
  edge_ordered : ∀ (p : Fin n × Fin n), p ∈ edgeSet → p.1 < p.2
  edgeSparsity : edgeSet.card < ((n : ℕ) * (n - 1)) / 2

namespace DGNGraph

variable {n : ℕ} (g : DGNGraph n)

def directedEdges : Finset (Fin n × Fin n) :=
  g.edgeSet ∪ g.edgeSet.image (fun ⟨i, j⟩ => ⟨j, i⟩)

def isEdge (i j : Fin n) : Prop := (i, j) ∈ g.directedEdges

def neighbors (i : Fin n) : Finset (Fin n) :=
  g.directedEdges.filter (fun ⟨a, _⟩ => a = i) |>.image Prod.snd

def edgeCount : ℕ := g.edgeSet.card

def Weight (n : ℕ) := Fin n → Fin n → ℝ
def State (n : ℕ) := Fin n → ℝ

def neighborWeightSum (w : Weight n) (x : State n) (φ : ℝ → ℝ) (g : DGNGraph n) (i : Fin n) : ℝ :=
  Finset.sum (g.neighbors i) fun j => w i j * φ (x j)

/-! ## δ-内聚划分定义 -/

/-- 顶点划分标签 -/
def Partition (n : ℕ) := Fin n → ℕ

/-- δ-内聚划分。

设 P 是顶点分组标签。称 P 是 δ-内聚划分，如果存在 θ_high > θ_low
使得 θ_high - θ_low ≥ δ > 0，且：
- 同组边权重 ≥ θ_high（内部内聚）
- 异组边权重 ≤ θ_low（外部分离） -/
structure CohesivePartition (n : ℕ) (g : DGNGraph n) (w : Weight n) where
  partition : Fin n → ℕ
  θ_high : ℝ
  θ_low : ℝ
  δ : ℝ
  h_theta_high_pos : θ_high > 0
  h_delta : θ_high - θ_low ≥ δ
  h_delta_pos : δ > 0
  h_intra : ∀ (i j : Fin n), g.isEdge i j → partition i = partition j → w i j ≥ θ_high
  h_inter : ∀ (i j : Fin n), g.isEdge i j → partition i ≠ partition j → w i j ≤ θ_low

/-- 图无反身性：`g.isEdge i i` 永假（无自环） -/
lemma isEdge_irreflexive {n : ℕ} (g : DGNGraph n) (i : Fin n) : ¬ g.isEdge i i := by
  unfold isEdge
  intro h
  rcases Finset.mem_union.mp h with (h' | h')
  · -- (i,i) ∈ edgeSet → 违反 edge_ordered
    have h_lt := g.edge_ordered (i,i) h'
    exact lt_irrefl i h_lt
  · -- (i,i) ∈ edgeSet.image swap → 存在 (a,b)∈edgeSet 使 swap(a,b)=(i,i)
    rcases Finset.mem_image.mp h' with ⟨⟨a,b⟩, ha, h_eq⟩
    have h_lt := g.edge_ordered (a,b) ha
    -- h_eq: Prod.swap (a,b) = (i,i)，即 (b,a) = (i,i)
    have h_eq_swap : (b, a) = (i, i) := by
      simpa using h_eq
    rcases Prod.mk.inj h_eq_swap with ⟨hb_eq_i, ha_eq_i⟩
    rw [ha_eq_i, hb_eq_i] at h_lt
    exact lt_irrefl i h_lt

end DGNGraph
