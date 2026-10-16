module

public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricMatrices
public import LeanResearch.RepulsiveCoulomb.DbarBranchWirtingerAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-! Literal coefficient-level Kähler cancellation for the actual graph of
1/Delta. The complex covector coefficients, their conjugation in H, and the
order of the complex Hessian are all explicit. -/
noncomputable section
open Set InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

def coulombReciprocalCoefficient {N : ℕ} (i : Fin N) (z : CoulombConfig N) : ℂ :=
  coulombReciprocalDerivative z (EuclideanSpace.single i 1)

theorem coulombReciprocal_contDiffAt {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    ContDiffAt ℂ (⊤ : ℕ∞) (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹) z :=
  ((coulombVandermonde_analyticAt z).inv hz).contDiffAt.of_le le_top

theorem coulombReciprocalCoefficient_contDiffAt {N : ℕ} (i : Fin N) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : ContDiffAt ℂ (⊤ : ℕ∞) (coulombReciprocalCoefficient i) z :=
  ((coulombReciprocal_contDiffAt hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

theorem coulombReciprocalCoefficient_hasFDerivAt {N : ℕ} (i : Fin N) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    HasFDerivAt (coulombReciprocalCoefficient i)
      ((fderiv ℂ (fderiv ℂ (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹)) z).flip
        (EuclideanSpace.single i 1)) z := by
  have hd := ((coulombReciprocal_contDiffAt hz).fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  change HasFDerivAt (fun y : CoulombConfig N =>
    (fderiv ℂ (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹) y)
      (EuclideanSpace.single i 1)) _ z
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using
    hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i 1) z)

theorem coulombReciprocalGraphMetric_entry {N : ℕ} (i j : Fin N) (z : CoulombConfig N) :
    dbarCLMMatrix (coulombReciprocalGraphMetric z) i j =
      (1 : Matrix (Fin N) (Fin N) ℂ) i j +
        conj (coulombReciprocalCoefficient i z) * coulombReciprocalCoefficient j z :=
  dbarCovectorMetric_matrix_entry (coulombReciprocalDerivative z) i j

theorem coulombReciprocalGraphMetric_entry_contDiffAt {N : ℕ} (i j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) i j) z := by
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (coulombReciprocalCoefficient i) z :=
    (coulombReciprocalCoefficient_contDiffAt i hz).restrict_scalars ℝ
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (coulombReciprocalCoefficient j) z :=
    (coulombReciprocalCoefficient_contDiffAt j hz).restrict_scalars ℝ
  have he : (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) i j) =
      fun w => (1 : Matrix (Fin N) (Fin N) ℂ) i j +
        conj (coulombReciprocalCoefficient i w) * coulombReciprocalCoefficient j w :=
    funext (coulombReciprocalGraphMetric_entry i j)
  rw [he]
  exact contDiffAt_const.add ((Complex.conjCLE.contDiff.contDiffAt.comp z hi).mul hj)

theorem coulombReciprocalGraphMetric_dbar_entry {N : ℕ} (i j k : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombDbarCoordinate (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) j k) z i =
      coulombReciprocalCoefficient k z *
        conj (fderiv ℂ (fderiv ℂ (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹)) z
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  have hj : DifferentiableAt ℂ (coulombReciprocalCoefficient j) z :=
    (coulombReciprocalCoefficient_contDiffAt j hz).differentiableAt (by simp)
  have hk : DifferentiableAt ℂ (coulombReciprocalCoefficient k) z :=
    (coulombReciprocalCoefficient_contDiffAt k hz).differentiableAt (by simp)
  have hcj : DifferentiableAt ℝ (fun w => conj (coulombReciprocalCoefficient j w)) z :=
    Complex.conjCLE.differentiableAt.comp z (hj.restrictScalars ℝ)
  have he : (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) j k) =
      fun w => (1 : Matrix (Fin N) (Fin N) ℂ) j k +
        conj (coulombReciprocalCoefficient j w) * coulombReciprocalCoefficient k w :=
    funext (coulombReciprocalGraphMetric_entry j k)
  rw [he, coulombDbarCoordinate_const_add, coulombDbarCoordinate_mul hcj (hk.restrictScalars ℝ),
    coulombDbarCoordinate_of_complex_differentiable hk, mul_zero, zero_add,
    coulombDbarCoordinate_conj (hj.restrictScalars ℝ), coulombDCoordinate_of_complex_differentiable hj,
    (coulombReciprocalCoefficient_hasFDerivAt j hz).fderiv]
  rfl

theorem coulombReciprocalGraphMetric_kahler {N : ℕ} (i j k : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombDbarCoordinate (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) j k) z i =
      coulombDbarCoordinate (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) i k) z j := by
  rw [coulombReciprocalGraphMetric_dbar_entry i j k hz, coulombReciprocalGraphMetric_dbar_entry j i k hz]
  rw [((coulombReciprocal_contDiffAt hz).isSymmSndFDerivAt (by simp)).eq
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]

end RepulsiveCoulomb
