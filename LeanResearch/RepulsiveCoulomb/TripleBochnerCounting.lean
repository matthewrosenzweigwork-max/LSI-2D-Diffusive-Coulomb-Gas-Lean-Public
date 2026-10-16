import LeanResearch.RepulsiveCoulomb.TripleGramBound

/-! Sharp global Bochner constant from exact triple incidence. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {α E : Type*} [Fintype α] [DecidableEq α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complete_graph_bochner_of_triples (hcard : 2 ≤ Fintype.card α)
    (v : Finset α → E) (a : Finset α → ℝ)
    (henergy : ∀ s ∈ Finset.univ.powersetCard 2, ‖v s‖ ^ 2 = 2 * a s)
    (hdis : ∀ s ∈ Finset.univ.powersetCard 2, ∀ r ∈ Finset.univ.powersetCard 2,
      Disjoint s r → 0 ≤ inner ℝ (v s) (v r))
    (hloc : ∀ t ∈ Finset.univ.powersetCard 3,
      3 * (∑ s ∈ t.powersetCard 2, a s) ≤ ‖∑ s ∈ t.powersetCard 2, v s‖ ^ 2) :
    (Fintype.card α : ℝ) * (∑ s ∈ Finset.univ.powersetCard 2, a s) ≤
      ‖∑ s ∈ Finset.univ.powersetCard 2, v s‖ ^ 2 := by
  have hsum := Finset.sum_le_sum hloc
  rw [← Finset.mul_sum, triple_edge_weighted_incidence, nsmul_eq_mul,
    Nat.cast_sub hcard, Nat.cast_ofNat] at hsum
  have hupper := triple_gram_bound hcard v hdis
  have he : (∑ s ∈ Finset.univ.powersetCard 2, ‖v s‖ ^ 2) =
      2 * ∑ s ∈ Finset.univ.powersetCard 2, a s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl henergy
  rw [he] at hupper
  nlinarith

end RepulsiveCoulomb
