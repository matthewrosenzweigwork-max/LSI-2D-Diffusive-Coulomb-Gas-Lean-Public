module

public import LeanResearch.RepulsiveCoulomb.FiniteTranspositionGap
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Actual Euclidean right-regular representation and its literal uniform average. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {G : Type*} [Group G] [Fintype G]

def finiteRightIsometry (g : G) : EuclideanSpace ℝ G ≃ₗᵢ[ℝ] EuclideanSpace ℝ G :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.mulRight g⁻¹)

theorem finiteRightIsometry_apply (g t : G) (x : EuclideanSpace ℝ G) :
    finiteRightIsometry g x t = x (t * g) := by
  simp [finiteRightIsometry, LinearIsometryEquiv.piLpCongrLeft_apply]

def finiteRightRepresentation : G →* (EuclideanSpace ℝ G →L[ℝ] EuclideanSpace ℝ G) where
  toFun g := (finiteRightIsometry g).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    ext t
    simp [finiteRightIsometry_apply]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    ext t
    change finiteRightIsometry (g * h) x t = finiteRightIsometry g (finiteRightIsometry h x) t
    simp [finiteRightIsometry_apply, mul_assoc]

theorem finiteRightRepresentation_apply (g t : G) (x : EuclideanSpace ℝ G) :
    finiteRightRepresentation g x t = x (t * g) := finiteRightIsometry_apply g t x

theorem finiteRightRepresentation_inner (g : G) (x y : EuclideanSpace ℝ G) :
    inner ℝ (finiteRightRepresentation g x) (finiteRightRepresentation g y) = inner ℝ x y :=
  (finiteRightIsometry g).inner_map_map x y

def finiteUniformMean (x : G → ℝ) : ℝ := (Fintype.card G : ℝ)⁻¹ * ∑ g, x g

theorem finiteRightRepresentation_average (x : EuclideanSpace ℝ G) (t : G) :
    finiteUnitaryAverage finiteRightRepresentation x t = finiteUniformMean x := by
  rw [finiteUnitaryAverage_apply]
  change (Fintype.card G : ℝ)⁻¹ * (∑ g, finiteRightRepresentation g x) t = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, finiteRightRepresentation_apply, finiteUniformMean]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)

theorem finiteRightRepresentation_error_norm (x : EuclideanSpace ℝ G) :
    ‖x - finiteUnitaryAverage finiteRightRepresentation x‖ ^ 2 =
      ∑ g, (x g - finiteUniformMean x) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply, finiteRightRepresentation_average]

theorem finiteRightRepresentation_difference_norm (x : EuclideanSpace ℝ G) (g : G) :
    ‖x - finiteRightRepresentation g x‖ ^ 2 = ∑ t, (x t - x (t * g)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply, finiteRightRepresentation_apply]

end RepulsiveCoulomb
