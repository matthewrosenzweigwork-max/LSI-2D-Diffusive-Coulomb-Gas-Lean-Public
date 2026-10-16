module

public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricMatrices
public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricNorms
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

/-! The actual inverse square-root coefficients are measurable and bounded,
including at points where the total derivative uses its standard default.
These statements concern fixed-fiber multiplication, not operator domains. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

def coulombInverseRootMatrix {N : ℕ} (z : CoulombConfig N) : Matrix (Fin N) (Fin N) ℂ :=
  dbarCLMMatrix (dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))

theorem dbarInverseRootMatrix_entry {N : ℕ} (a : CoulombConfig N) (i j : Fin N) :
    dbarCLMMatrix (dbarGraphMetricInverseRoot a) i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j -
      (((dbarGraphMetricRootScalar a * (1 + dbarGraphMetricRootScalar a))⁻¹ : ℝ) : ℂ) *
        (a i * conj (a j)) := by
  unfold dbarGraphMetricInverseRoot
  rw [dbarCLMMatrix, dbarRankOnePerturbation_apply]
  simp [EuclideanSpace.single, EuclideanSpace.inner_single_right, Matrix.one_apply, eq_comm]
  ring

theorem dbarInverseRootMatrix_entry_continuous {N : ℕ} (i j : Fin N) :
    Continuous (fun a : CoulombConfig N => dbarCLMMatrix (dbarGraphMetricInverseRoot a) i j) := by
  have ht : Continuous (dbarGraphMetricRootScalar (N := N)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))
  have hden : ∀ a : CoulombConfig N,
      dbarGraphMetricRootScalar a * (1 + dbarGraphMetricRootScalar a) ≠ 0 := by
    intro a
    exact mul_ne_zero (dbarGraphMetricRootScalar_pos a).ne' (ne_of_gt (by have hp := dbarGraphMetricRootScalar_pos a; linarith))
  have hc := Complex.continuous_ofReal.comp ((ht.mul (continuous_const.add ht)).inv₀ hden)
  have hi : Continuous (fun a : CoulombConfig N => a i) := (EuclideanSpace.proj (𝕜 := ℂ) i).continuous
  have hj : Continuous (fun a : CoulombConfig N => a j) := (EuclideanSpace.proj (𝕜 := ℂ) j).continuous
  have he : (fun a : CoulombConfig N => dbarCLMMatrix (dbarGraphMetricInverseRoot a) i j) =
      fun a => (1 : Matrix (Fin N) (Fin N) ℂ) i j -
        (((dbarGraphMetricRootScalar a * (1 + dbarGraphMetricRootScalar a))⁻¹ : ℝ) : ℂ) * (a i * conj (a j)) :=
    funext (fun a => dbarInverseRootMatrix_entry a i j)
  rw [he]
  exact continuous_const.sub (hc.mul (hi.mul (Complex.conjCLE.continuous.comp hj)))

theorem dbarCovectorRiesz_continuous (N : ℕ) :
    Continuous (dbarCovectorRiesz (N := N)) :=
  ContinuousLinearMap.adjoint.continuous.clm_apply continuous_const

theorem coulombInverseRootMatrix_entry_measurable {N : ℕ} (i j : Fin N) :
    Measurable (fun z : CoulombConfig N => coulombInverseRootMatrix z i j) := by
  have hA : Measurable (coulombReciprocalDerivative (N := N)) :=
    measurable_fderiv ℂ (fun w : CoulombConfig N => (coulombVandermonde w)⁻¹)
  exact (dbarInverseRootMatrix_entry_continuous i j).measurable.comp
    ((dbarCovectorRiesz_continuous N).measurable.comp hA)

theorem coulombInverseRootMatrix_entry_norm_le_one {N : ℕ} (z : CoulombConfig N) (i j : Fin N) :
    ‖coulombInverseRootMatrix z i j‖ ≤ 1 := by
  change ‖(dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
    (EuclideanSpace.single j 1)) i‖ ≤ 1
  calc
    _ ≤ ‖dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (EuclideanSpace.single j 1)‖ :=
      PiLp.norm_apply_le _ i
    _ ≤ ‖(EuclideanSpace.single j 1 : CoulombConfig N)‖ :=
      dbarCovectorMetricInverseRoot_contraction (coulombReciprocalDerivative z) _
    _ = 1 := by simp

theorem coulombInverseRootMatrix_entry_memLp_top {N : ℕ} (β : ℝ) (i j : Fin N) :
    MemLp (fun z : CoulombConfig N => coulombInverseRootMatrix z i j) ⊤ (coulombMeasure N β) :=
  memLp_top_of_bound (coulombInverseRootMatrix_entry_measurable i j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => coulombInverseRootMatrix_entry_norm_le_one z i j)

end RepulsiveCoulomb
