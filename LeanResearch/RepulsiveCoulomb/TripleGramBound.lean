import LeanResearch.RepulsiveCoulomb.TripleGramCounting

/-! UNTESTED DRAFT: Gram bound from nonnegative disjoint-edge cross terms. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {α E : Type*} [Fintype α] [DecidableEq α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sum_sq_double_inner {ι : Type*} (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [sum_inner]
  simp only [inner_sum]

theorem triple_gram_bound (hcard : 2 ≤ Fintype.card α) (v : Finset α → E)
    (hdis : ∀ s ∈ Finset.univ.powersetCard 2, ∀ r ∈ Finset.univ.powersetCard 2,
      Disjoint s r → 0 ≤ inner ℝ (v s) (v r)) :
    (∑ t ∈ Finset.univ.powersetCard 3, ‖∑ s ∈ t.powersetCard 2, v s‖ ^ 2) ≤
      ‖∑ s ∈ Finset.univ.powersetCard 2, v s‖ ^ 2 +
        ((Fintype.card α : ℝ) - 3) * ∑ s ∈ Finset.univ.powersetCard 2, ‖v s‖ ^ 2 := by
  classical
  simp_rw [norm_sum_sq_double_inner]
  rw [triple_edge_pair_incidence]
  have hp : ∀ s ∈ Finset.univ.powersetCard 2, ∀ r ∈ Finset.univ.powersetCard 2,
      ((tripleSupersets (s ∪ r)).card : ℝ) * inner ℝ (v s) (v r) ≤
        inner ℝ (v s) (v r) +
          if s = r then ((Fintype.card α : ℝ) - 3) * ‖v s‖ ^ 2 else 0 := by
    intro s hs r hr
    rw [tripleSupersets_card_edge_union (Finset.mem_powersetCard.mp hs).2
      (Finset.mem_powersetCard.mp hr).2]
    by_cases he : s = r
    · subst r
      simp only [ite_true, real_inner_self_eq_norm_sq, Nat.cast_sub hcard, Nat.cast_ofNat]
      ring_nf
      exact le_rfl
    · simp only [if_neg he, add_zero]
      by_cases hd : Disjoint s r
      · simp only [if_pos hd, Nat.cast_zero, zero_mul]
        exact hdis s hs r hr hd
      · simp only [if_neg hd, Nat.cast_one, one_mul, le_refl]
  have hsum := Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun r hr => hp s hs r hr
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_mul,
    ← Finset.mul_sum] using hsum

end RepulsiveCoulomb
