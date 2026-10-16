module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveDomain
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyWeakLSC
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPositiveIntegralLSC
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

@[expose] public section

/-! Genuine weak lower semicontinuity of the complete nonnegative objective on
all planar probability measures. No moment, density or entropy finiteness is
assumed along the converging measures. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem lintegral_equilibriumExtendedKernel_eq_iSup (μ : Measure (ℂ × ℂ)) :
    (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ) =
      ⨆ n : ℕ, ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (equilibriumShiftedKernelApprox n p) ∂μ := by
  apply lintegral_iSup
  · intro n
    exact (equilibriumShiftedKernelApprox_continuous n).measurable.ennreal_ofReal
  · intro n m hnm p
    exact ENNReal.ofReal_le_ofReal (equilibriumShiftedKernelApprox_monotone p hnm)

/-- The genuine extended singular interaction, with infinite diagonal, is weakly
lsc after the exact nonnegative logarithmic shift. -/
theorem equilibriumExtendedInteraction_lowerSemicontinuous :
    LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      ∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂(μ : Measure ℂ).prod μ) := by
  have hp : Continuous (fun μ : ProbabilityMeasure ℂ => μ.prod μ) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have he : (fun μ : ProbabilityMeasure ℂ =>
      ∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂(μ : Measure ℂ).prod μ) =
      (fun μ : ProbabilityMeasure ℂ => ⨆ n : ℕ,
        ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (equilibriumShiftedKernelApprox n p) ∂(μ.prod μ)) := by
    funext μ
    exact lintegral_equilibriumExtendedKernel_eq_iSup ((μ : Measure ℂ).prod μ)
  rw [he]
  apply lowerSemicontinuous_iSup
  intro n
  exact (equilibrium_positiveIntegral_lowerSemicontinuous (equilibriumShiftedKernelApprox n)
    (equilibriumShiftedKernelApprox_continuous n) (equilibriumShiftedKernelApprox_nonneg n)).comp hp

/-- Actual lsc of the complete objective, including infinite entropy and
interaction and singular/non-P2 probability measures. -/
theorem equilibriumObjective_lowerSemicontinuous {β : ℝ} (hβ : 0 < β) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ => equilibriumNonnegativeObjective β μ) := by
  have ha : 0 < β / 4 := by positivity
  letI := equilibriumGaussianMeasure_probability ha
  have he := equilibrium_klDiv_weak_lowerSemicontinuous (equilibriumGaussianMeasure (β / 4))
  have hew : LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      ENNReal.ofReal β⁻¹ * InformationTheory.klDiv (μ : Measure ℂ) (equilibriumGaussianMeasure (β / 4))) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous he
      (fun x y hxy => mul_le_mul_right hxy _)
  have hkw : LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂(μ : Measure ℂ).prod μ)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      equilibriumExtendedInteraction_lowerSemicontinuous (fun x y hxy => mul_le_mul_right hxy _)
  have hc := equilibrium_positiveIntegral_lowerSemicontinuous equilibriumShiftedConfinement
    equilibriumShiftedConfinement_continuous equilibriumShiftedConfinement_nonneg
  exact (hew.add hkw).add hc

theorem equilibriumObjective_sublevel_isClosed {β : ℝ} (hβ : 0 < β) (C : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure ℂ | equilibriumNonnegativeObjective β μ ≤ C} :=
  (equilibriumObjective_lowerSemicontinuous hβ).isClosed_preimage C

end RepulsiveCoulomb
