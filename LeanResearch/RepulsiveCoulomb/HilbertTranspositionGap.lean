module

public import LeanResearch.RepulsiveCoulomb.FiniteOrbitSpan
public import LeanResearch.RepulsiveCoulomb.OrderedEdgeSum

@[expose] public section

/-! The sharp transposition bound in an arbitrary real Hilbert representation. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hilbert_transposition_gap_norm (hN : 2 ≤ N)
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    2 * (N : ℝ) * ‖x - finiteUnitaryAverage U x‖ ^ 2 ≤
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, ‖x - U (edgeTransposition s) x‖ ^ 2 := by
  let y : finiteOrbitSpan U x := ⟨x, finiteOrbitSpan_self U x⟩
  have h := finite_transposition_gap_norm hN (finiteOrbitRepresentation U x)
    (finiteOrbitRepresentation_inner U x hU) y
  change 2 * (N : ℝ) * ‖x - (finiteUnitaryAverage (finiteOrbitRepresentation U x) y : E)‖ ^ 2 ≤
    ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, ‖x - U (edgeTransposition s) x‖ ^ 2 at h
  rw [finiteOrbitRepresentation_average_coe] at h
  exact h

theorem hilbert_transposition_gap_pairs (hN : 2 ≤ N)
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    2 * (N : ℝ) * ‖x - finiteUnitaryAverage U x‖ ^ 2 ≤
      ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
        ‖x - U (Equiv.swap p.1 p.2) x‖ ^ 2 := by
  have h := hilbert_transposition_gap_norm hN U hU x
  rw [← ordered_pair_edge_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [edgeTransposition_pair p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)]

end RepulsiveCoulomb
