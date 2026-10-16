import LeanResearch.RepulsiveCoulomb.TriplePermutationAlgebra

/-! Exact local S3 Bochner inequality, proved by the alternating orthogonal projection. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def tripleLaplacian (U : TriplePerm →* (E →L[ℝ] E)) : E →L[ℝ] E :=
  (1 - U tripleA) + (1 - U tripleB) + (1 - U tripleC)

theorem tripleLaplacian_apply (U : TriplePerm →* (E →L[ℝ] E)) (x : E) :
    tripleLaplacian U x = (x - U tripleA x) + (x - U tripleB x) + (x - U tripleC x) := by
  simp [tripleLaplacian]

theorem unitaryRep_mul_apply {G : Type*} [Monoid G] (U : G →* (E →L[ℝ] E))
    (g h : G) (x : E) : U g (U h x) = U (g * h) x := by
  rw [map_mul]
  rfl

theorem tripleAlternatingAverage_apply (U : TriplePerm →* (E →L[ℝ] E)) (x : E) :
    finiteUnitaryAverage (realCharacterTwist U (permSignReal 3)) x =
      (1 / 6 : ℝ) • (x - U tripleA x - U tripleB x - U tripleC x +
        U tripleR x + U tripleRinv x) := by
  rw [finiteUnitaryAverage_apply, triplePerm_sum]
  simp only [realCharacterTwist_apply, map_one, ContinuousLinearMap.one_apply,
    tripleSignA, tripleSignB, tripleSignC, tripleSignR, tripleSignRinv, one_smul, neg_one_smul]
  norm_num [Fintype.card_perm, Fintype.card_fin, Nat.factorial]
  module

theorem tripleLaplacian_selfAdjoint (U : TriplePerm →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x y : E) :
    inner ℝ (tripleLaplacian U x) y = inner ℝ x (tripleLaplacian U y) := by
  simp only [tripleLaplacian_apply, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
    finiteUnitary_inner_flip U hU, tripleA_inv, tripleB_inv, tripleC_inv]

theorem tripleLaplacian_bochner_identity (U : TriplePerm →* (E →L[ℝ] E)) (x : E) :
    tripleLaplacian U (tripleLaplacian U x) - (3 : ℝ) • tripleLaplacian U x =
      (18 : ℝ) • finiteUnitaryAverage (realCharacterTwist U (permSignReal 3)) x := by
  rw [tripleAlternatingAverage_apply]
  simp only [tripleLaplacian_apply, map_add, map_sub, unitaryRep_mul_apply,
    tripleA_sq, tripleB_sq, tripleC_sq, tripleAB, tripleBA, tripleAC, tripleCA,
    tripleBC, tripleCB, map_one, ContinuousLinearMap.one_apply]
  module

theorem tripleLaplacian_bochner (U : TriplePerm →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y) (x : E) :
    3 * inner ℝ x (tripleLaplacian U x) ≤ ‖tripleLaplacian U x‖ ^ 2 := by
  have hs := tripleLaplacian_selfAdjoint U hU x (tripleLaplacian U x)
  rw [real_inner_self_eq_norm_sq] at hs
  have h := congrArg (fun y => inner ℝ x y) (tripleLaplacian_bochner_identity U x)
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, ← hs] at h
  have hp := finiteUnitaryAverage_inner_eq_norm_sq (realCharacterTwist U (permSignReal 3))
    (realCharacterTwist_inner U (permSignReal 3) hU (permSignReal_sq 3)) x
  rw [hp] at h
  nlinarith [sq_nonneg ‖finiteUnitaryAverage (realCharacterTwist U (permSignReal 3)) x‖]

end RepulsiveCoulomb
