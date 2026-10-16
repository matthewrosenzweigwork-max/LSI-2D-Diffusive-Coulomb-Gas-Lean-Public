import LeanResearch.RepulsiveCoulomb.EdgeTransposition
import LeanResearch.RepulsiveCoulomb.TripleBochnerCounting

/-! The sharp Bochner inequality for all complete-graph transpositions. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transpositionLaplacian (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E)) : E →L[ℝ] E :=
  ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, unitaryDifference U (edgeTransposition s)

theorem transpositionLaplacian_apply (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E)) (x : E) :
    transpositionLaplacian U x =
      ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, unitaryDifference U (edgeTransposition s) x := by
  simp [transpositionLaplacian]

theorem transpositionLaplacian_positive (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    0 ≤ inner ℝ x (transpositionLaplacian U x) := by
  rw [transpositionLaplacian_apply, inner_sum]
  exact Finset.sum_nonneg fun s _ => unitaryDifference_positive U hU _ x

theorem transpositionLaplacian_selfAdjoint (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x y : E) :
    inner ℝ (transpositionLaplacian U x) y = inner ℝ x (transpositionLaplacian U y) := by
  simp only [transpositionLaplacian_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun s _ => unitaryDifference_selfAdjoint U hU _ (edgeTransposition_inv s) x y

theorem transpositionLaplacian_bochner (hN : 2 ≤ N)
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    (N : ℝ) * inner ℝ x (transpositionLaplacian U x) ≤ ‖transpositionLaplacian U x‖ ^ 2 := by
  rw [transpositionLaplacian_apply, inner_sum]
  have hcard : (N : ℝ) = (Fintype.card (Fin N) : ℝ) := by simp
  rw [hcard]
  apply complete_graph_bochner_of_triples (by simpa using hN)
    (fun s => unitaryDifference U (edgeTransposition s) x)
    (fun s => inner ℝ x (unitaryDifference U (edgeTransposition s) x))
  · intro s hs
    exact (unitaryDifference_energy U hU _ x).symm
  · intro s hs r hr hd
    obtain ⟨i,j,hij,hs',hes⟩ := edgeTransposition_endpoints s (Finset.mem_powersetCard.mp hs).2
    obtain ⟨k,l,hkl,hr',her⟩ := edgeTransposition_endpoints r (Finset.mem_powersetCard.mp hr).2
    have hc : i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l := by
      simpa [hs', hr', Finset.disjoint_left, and_assoc] using hd
    rw [hes, her]
    apply transposition_disjoint_cross_nonneg U hU i j k l
    simp [List.nodup_cons, hij, hkl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  · intro t ht
    obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp (Finset.mem_powersetCard.mp ht).2
    rw [sum_triple_edges _ i j k hij hik hjk, sum_triple_edges _ i j k hij hik hjk]
    simp only [edgeTransposition_pair i j hij, edgeTransposition_pair i k hik,
      edgeTransposition_pair j k hjk, ← inner_add_right]
    exact transposition_triple_bochner U hU i j k hij hik hjk x

end RepulsiveCoulomb
