module

public import LeanResearch.RepulsiveCoulomb.FinitePermutationPoincare

@[expose] public section

/-! Identification of unordered edges with pairs i<j, without multiplicity loss. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

theorem ordered_pair_edge_sum {α A : Type*} [Fintype α] [LinearOrder α] [AddCommMonoid A]
    (w : Finset α → A) :
    (∑ p ∈ (Finset.univ : Finset (α × α)).filter (fun p => p.1 < p.2), w {p.1,p.2}) =
      ∑ s ∈ (Finset.univ : Finset α).powersetCard 2, w s := by
  classical
  apply Finset.sum_bij (fun p _ => ({p.1,p.2} : Finset α))
  · intro p hp
    have hlt := (Finset.mem_filter.mp hp).2
    simp [Finset.mem_powersetCard, ne_of_lt hlt]
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have he' : ({p.1,p.2} : Set α) = {q.1,q.2} := by
      simpa only [Finset.coe_pair] using congrArg (fun s : Finset α => (s : Set α)) he
    rcases Set.pair_eq_pair_iff.mp he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Prod.ext h1 h2
    · rw [h1,h2] at hp'
      exact (lt_asymm hp' hq').elim
  · intro s hs
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨(i,j), by simp [hlt], rfl⟩
    · exact ⟨(j,i), by simp [hlt], Finset.pair_comm j i⟩
  · intro p hp
    rfl

theorem finite_permutation_poincare_pairs {N : ℕ} (hN : 2 ≤ N)
    (f : Equiv.Perm (Fin N) → ℝ) :
    finiteUniformMean (fun σ => (f σ - finiteUniformMean f) ^ 2) ≤
      (1 / (2 * (N : ℝ))) *
        ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
          finiteUniformMean (fun σ => (f σ - f (σ * Equiv.swap p.1 p.2)) ^ 2) := by
  have h := finite_permutation_poincare hN f
  rw [← ordered_pair_edge_sum] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [edgeTransposition_pair p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)]

end RepulsiveCoulomb
