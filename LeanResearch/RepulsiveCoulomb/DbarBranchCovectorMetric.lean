import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricAlgebra
import LeanResearch.RepulsiveCoulomb.CoulombExhaustionGeometry

/-! The graph metric of an actual complex covector is I + A†A. Its rank-one
vector is the complex Hilbert representer A†1, whose coordinates are the
conjugates of the derivative coefficients. Algebra only: no domain or curvature
estimate is claimed. -/
noncomputable section
open InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

def dbarCovectorRiesz {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) : CoulombConfig N := A.adjoint 1

theorem dbarCovectorRiesz_inner {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    inner ℂ (dbarCovectorRiesz A) v = A v := by
  rw [dbarCovectorRiesz, ContinuousLinearMap.adjoint_inner_left]
  simp

theorem dbarCovectorRiesz_innerSL {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) :
    innerSL ℂ (dbarCovectorRiesz A) = A := by
  ext v
  exact dbarCovectorRiesz_inner A v

theorem dbarCovectorRiesz_coordinate {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (i : Fin N) :
    dbarCovectorRiesz A i = conj (A (EuclideanSpace.single i 1)) := by
  have h := congrArg conj (dbarCovectorRiesz_inner A (EuclideanSpace.single i 1))
  simpa [EuclideanSpace.inner_single_right] using h

theorem dbarCovectorRiesz_norm {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) :
    ‖dbarCovectorRiesz A‖ = ‖A‖ := by
  calc
    _ = ‖innerSL ℂ (dbarCovectorRiesz A)‖ :=
      (innerSL_apply_norm ℂ (dbarCovectorRiesz A)).symm
    _ = ‖A‖ := congrArg norm (dbarCovectorRiesz_innerSL A)

def dbarCovectorMetric {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  ContinuousLinearMap.id ℂ _ + A.adjoint.comp A

def dbarCovectorMetricInverse {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  dbarGraphMetricInverse (dbarCovectorRiesz A)

theorem dbarCovectorMetric_eq_rankOne {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) :
    dbarCovectorMetric A = dbarGraphMetric (dbarCovectorRiesz A) := by
  have hAA : A.adjoint.comp A = rankOne ℂ (dbarCovectorRiesz A) (dbarCovectorRiesz A) := by
    calc
      _ = (innerSL ℂ (dbarCovectorRiesz A)).adjoint.comp (innerSL ℂ (dbarCovectorRiesz A)) := by
        rw [dbarCovectorRiesz_innerSL]
      _ = _ := by rw [ContinuousLinearMap.adjoint_innerSL_apply]; rfl
  exact congrArg (fun B => ContinuousLinearMap.id ℂ (CoulombConfig N) + B) hAA

theorem dbarCovectorMetric_quadratic {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    (inner ℂ v (dbarCovectorMetric A v)).re = ‖v‖ ^ 2 + ‖A v‖ ^ 2 := by
  change (inner ℂ v (v + A.adjoint (A v))).re = _
  rw [inner_add_right, Complex.add_re, ContinuousLinearMap.adjoint_inner_right]
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hAv : (inner ℂ (A v) (A v)).re = ‖A v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (A v)
  rw [hv, hAv]

theorem dbarCovectorMetric_lower {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    ‖v‖ ^ 2 ≤ (inner ℂ v (dbarCovectorMetric A v)).re := by
  rw [dbarCovectorMetric_quadratic]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem dbarCovectorMetric_right_inverse {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    dbarCovectorMetric A (dbarCovectorMetricInverse A v) = v := by
  rw [dbarCovectorMetric_eq_rankOne]
  exact dbarGraphMetric_right_inverse _ _

theorem dbarCovectorMetric_left_inverse {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    dbarCovectorMetricInverse A (dbarCovectorMetric A v) = v := by
  rw [dbarCovectorMetric_eq_rankOne]
  exact dbarGraphMetric_left_inverse _ _

def coulombReciprocalDerivative {N : ℕ} (z : CoulombConfig N) : CoulombConfig N →L[ℂ] ℂ :=
  fderiv ℂ (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹) z

theorem coulombReciprocal_hasFDerivAt {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    HasFDerivAt (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹)
      (coulombReciprocalDerivative z) z :=
  (((coulombVandermonde_analyticAt z).inv hz).differentiableAt).hasFDerivAt

def coulombReciprocalGraphMetric {N : ℕ} (z : CoulombConfig N) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  dbarCovectorMetric (coulombReciprocalDerivative z)

theorem coulombReciprocalGraphMetric_quadratic {N : ℕ} (z v : CoulombConfig N) :
    (inner ℂ v (coulombReciprocalGraphMetric z v)).re =
      ‖v‖ ^ 2 + ‖coulombReciprocalDerivative z v‖ ^ 2 :=
  dbarCovectorMetric_quadratic _ _

end RepulsiveCoulomb
