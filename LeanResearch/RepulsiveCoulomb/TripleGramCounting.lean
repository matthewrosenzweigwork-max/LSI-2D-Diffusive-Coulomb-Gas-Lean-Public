import LeanResearch.RepulsiveCoulomb.TripleCounting
import Mathlib.Analysis.InnerProductSpace.Basic

/-! UNTESTED DRAFT: exact triple incidence applied to ordered pairs of edges. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem triple_edge_pair_incidence (w : Finset α → Finset α → ℝ) :
    (∑ t ∈ Finset.univ.powersetCard 3,
      ∑ s ∈ t.powersetCard 2, ∑ r ∈ t.powersetCard 2, w s r) =
      ∑ s ∈ Finset.univ.powersetCard 2, ∑ r ∈ Finset.univ.powersetCard 2,
        ((tripleSupersets (s ∪ r)).card : ℝ) * w s r := by
  classical
  conv_lhs =>
    arg 2
    ext t
    rw [local_edges_eq_filter t]
    simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hi : ∀ t : Finset α,
      (if s ⊆ t then if r ⊆ t then w s r else 0 else 0) =
        if s ∪ r ⊆ t then w s r else 0 := by
    intro t
    simp only [Finset.union_subset_iff]
    split_ifs <;> simp_all
  simp_rw [hi]
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [tripleSupersets, nsmul_eq_mul]

end RepulsiveCoulomb
