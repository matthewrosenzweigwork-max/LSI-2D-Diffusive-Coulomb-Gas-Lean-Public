module

public import LeanResearch.RepulsiveCoulomb.TripleBochner
public import LeanResearch.RepulsiveCoulomb.UnitaryDifferences
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Perm.Support

@[expose] public section

/-! Exact transport of the local three-label inequality to arbitrary labels. -/
noncomputable section
open InnerProductSpace
namespace RepulsiveCoulomb

theorem permViaEmbedding_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ι : α ↪ β) (a b : α) :
    Equiv.Perm.viaEmbeddingHom ι (Equiv.swap a b) = Equiv.swap (ι a) (ι b) := by
  classical
  ext z
  by_cases hz : z ∈ Set.range ι
  · obtain ⟨x, rfl⟩ := hz
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]
    exact (ι.injective.swap_apply a b x).symm
  · rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hz,
      Equiv.swap_apply_of_ne_of_ne (fun h => hz ⟨a, h.symm⟩) (fun h => hz ⟨b, h.symm⟩)]

def tripleLabelEmbedding {N : ℕ} (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Fin 3 ↪ Fin N :=
  ⟨![i, j, k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

theorem tripleLabelEmbedding_zero {N : ℕ} (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripleLabelEmbedding i j k hij hik hjk 0 = i := rfl
theorem tripleLabelEmbedding_one {N : ℕ} (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripleLabelEmbedding i j k hij hik hjk 1 = j := rfl
theorem tripleLabelEmbedding_two {N : ℕ} (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tripleLabelEmbedding i j k hij hik hjk 2 = k := rfl

theorem transposition_triple_bochner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y)
    (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : E) :
    3 * inner ℝ x (unitaryDifference U (Equiv.swap i j) x +
      unitaryDifference U (Equiv.swap j k) x + unitaryDifference U (Equiv.swap i k) x) ≤
      ‖unitaryDifference U (Equiv.swap i j) x +
        unitaryDifference U (Equiv.swap j k) x + unitaryDifference U (Equiv.swap i k) x‖ ^ 2 := by
  let ι := tripleLabelEmbedding i j k hij hik hjk
  let V := U.comp (Equiv.Perm.viaEmbeddingHom ι)
  have hV : ∀ g x y, inner ℝ (V g x) (V g y) = inner ℝ x y :=
    fun g x y => hU _ x y
  have h := tripleLaplacian_bochner V hV x
  simpa only [tripleLaplacian_apply, V, MonoidHom.comp_apply, tripleA, tripleB, tripleC,
    permViaEmbedding_swap, ι, tripleLabelEmbedding_zero, tripleLabelEmbedding_one,
    tripleLabelEmbedding_two, unitaryDifference_apply] using h

theorem transposition_disjoint_cross_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y)
    (i j k l : Fin N) (hd : [i, j, k, l].Nodup) (x : E) :
    0 ≤ inner ℝ (unitaryDifference U (Equiv.swap i j) x) (unitaryDifference U (Equiv.swap k l) x) :=
  unitaryDifference_disjoint_cross_nonneg U hU _ _ (Equiv.swap_inv i j) (Equiv.swap_inv k l)
    (Equiv.Perm.disjoint_swap_swap hd).commute.eq x

end RepulsiveCoulomb
