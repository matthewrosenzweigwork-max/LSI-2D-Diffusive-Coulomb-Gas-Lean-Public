module

public import LeanResearch.RepulsiveCoulomb.SignedUnitary
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

/-! The six permutations of three labels and their exact multiplication data. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

abbrev TriplePerm := Equiv.Perm (Fin 3)
def tripleA : TriplePerm := Equiv.swap 0 1
def tripleB : TriplePerm := Equiv.swap 1 2
def tripleC : TriplePerm := Equiv.swap 0 2
def tripleR : TriplePerm := tripleA * tripleB
def tripleRinv : TriplePerm := tripleB * tripleA

theorem triplePerm_univ :
    (Finset.univ : Finset TriplePerm) = {1, tripleA, tripleB, tripleC, tripleR, tripleRinv} := by
  have hs : ({1, tripleA, tripleB, tripleC, tripleR, tripleRinv} : Finset TriplePerm).card = 6 := by decide
  have hu : (Finset.univ : Finset TriplePerm).card = 6 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  exact (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by rw [hs, hu])).symm

theorem triplePerm_sum {E : Type*} [AddCommMonoid E] (f : TriplePerm → E) :
    (∑ σ : TriplePerm, f σ) =
      f 1 + f tripleA + f tripleB + f tripleC + f tripleR + f tripleRinv := by
  rw [triplePerm_univ]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

theorem tripleA_sq : tripleA * tripleA = 1 := by decide
theorem tripleB_sq : tripleB * tripleB = 1 := by decide
theorem tripleC_sq : tripleC * tripleC = 1 := by decide
theorem tripleAB : tripleA * tripleB = tripleR := rfl
theorem tripleBA : tripleB * tripleA = tripleRinv := rfl
theorem tripleAC : tripleA * tripleC = tripleRinv := by decide
theorem tripleCA : tripleC * tripleA = tripleR := by decide
theorem tripleBC : tripleB * tripleC = tripleR := by decide
theorem tripleCB : tripleC * tripleB = tripleRinv := by decide
theorem tripleA_inv : tripleA⁻¹ = tripleA := by decide
theorem tripleB_inv : tripleB⁻¹ = tripleB := by decide
theorem tripleC_inv : tripleC⁻¹ = tripleC := by decide

theorem tripleSignA : permSignReal 3 tripleA = -1 :=
  permSignReal_swap 0 1 (by decide)
theorem tripleSignB : permSignReal 3 tripleB = -1 :=
  permSignReal_swap 1 2 (by decide)
theorem tripleSignC : permSignReal 3 tripleC = -1 :=
  permSignReal_swap 0 2 (by decide)
theorem tripleSignR : permSignReal 3 tripleR = 1 := by
  rw [tripleR, map_mul, tripleSignA, tripleSignB]
  norm_num
theorem tripleSignRinv : permSignReal 3 tripleRinv = 1 := by
  rw [tripleRinv, map_mul, tripleSignB, tripleSignA]
  norm_num

end RepulsiveCoulomb
