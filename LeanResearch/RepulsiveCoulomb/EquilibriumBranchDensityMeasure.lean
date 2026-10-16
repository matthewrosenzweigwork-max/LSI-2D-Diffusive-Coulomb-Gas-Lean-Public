import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGaussian
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Literal density measures and the exact Gaussian RN representation needed
for the full extended entropy correspondence. No positive-entropy finiteness
is required by the KL integral identity. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumDensityMeasure (ρ : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

def equilibriumGaussianMeasure (a : ℝ) : Measure ℂ :=
  equilibriumDensityMeasure (equilibriumGaussian a)

theorem equilibriumDensityMeasure_probability {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1) :
    IsProbabilityMeasure (equilibriumDensityMeasure ρ) := by
  constructor
  rw [equilibriumDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hρi
      (Eventually.of_forall hρ0), hρmass, ENNReal.ofReal_one]

theorem equilibriumGaussianMeasure_probability {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (equilibriumGaussianMeasure a) :=
  equilibriumDensityMeasure_probability (fun x => (equilibriumGaussian_pos ha x).le)
    (equilibriumGaussian_integrable ha) (integral_equilibriumGaussian ha)

theorem equilibriumDensityMeasure_absolutelyContinuous (ρ : ℂ → ℝ) :
    equilibriumDensityMeasure ρ ≪ volume := withDensity_absolutelyContinuous _ _

theorem volume_absolutelyContinuous_equilibriumGaussianMeasure {a : ℝ} (ha : 0 < a) :
    (volume : Measure ℂ) ≪ equilibriumGaussianMeasure a :=
  withDensity_absolutelyContinuous' (equilibriumGaussian_continuous a).measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall (fun x => (ENNReal.ofReal_pos.mpr (equilibriumGaussian_pos ha x)).ne'))

theorem equilibriumDensityMeasure_integrable_iff {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : ℂ → ℝ) :
    Integrable f (equilibriumDensityMeasure ρ) ↔ Integrable (fun x => f x * ρ x) := by
  simpa only [equilibriumDensityMeasure, ENNReal.toReal_ofReal (hρ0 _)] using
    (integrable_withDensity_iff hρm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := f))

theorem integral_equilibriumDensityMeasure {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : ℂ → ℝ) :
    (∫ x, f x ∂equilibriumDensityMeasure ρ) = ∫ x : ℂ, ρ x * f x := by
  simpa only [equilibriumDensityMeasure, ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

/-- Actual measure identity giving the Gaussian relative density, including
zeros of rho and without assuming its logarithm is integrable. -/
theorem equilibriumDensityMeasure_eq_gaussian_withDensity {a : ℝ} (ha : 0 < a)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    equilibriumDensityMeasure ρ = (equilibriumGaussianMeasure a).withDensity
      (fun x => ENNReal.ofReal (ρ x / equilibriumGaussian a x)) := by
  have hγ := (equilibriumGaussian_continuous a).measurable
  have hr : Measurable (fun x => ρ x / equilibriumGaussian a x) := hρm.div hγ
  have hid : (fun x => ENNReal.ofReal (equilibriumGaussian a x)) *
      (fun x => ENNReal.ofReal (ρ x / equilibriumGaussian a x)) =
        (fun x => ENNReal.ofReal (ρ x)) := by
    funext x
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (equilibriumGaussian_pos ha x).le]
    congr 1
    field_simp [(equilibriumGaussian_pos ha x).ne']
  unfold equilibriumGaussianMeasure equilibriumDensityMeasure
  rw [← withDensity_mul volume hγ.ennreal_ofReal hr.ennreal_ofReal, hid]

/-- The exact KL integral on the whole probability-density domain; infinity
is retained if the relative entropy is infinite. -/
theorem equilibriumGaussian_klDiv_density {a : ℝ} (ha : 0 < a) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) :
    InformationTheory.klDiv (equilibriumDensityMeasure ρ) (equilibriumGaussianMeasure a) =
      ∫⁻ x : ℂ, ENNReal.ofReal (equilibriumGaussian a x *
        InformationTheory.klFun (ρ x / equilibriumGaussian a x)) := by
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  letI := equilibriumGaussianMeasure_probability ha
  have hγ := (equilibriumGaussian_continuous a).measurable
  have hr : Measurable (fun x => ρ x / equilibriumGaussian a x) := hρm.div hγ
  have he := equilibriumDensityMeasure_eq_gaussian_withDensity ha hρm hρ0
  have hac : equilibriumDensityMeasure ρ ≪ equilibriumGaussianMeasure a := by
    rw [he]
    exact withDensity_absolutelyContinuous _ _
  have hRN : (equilibriumDensityMeasure ρ).rnDeriv (equilibriumGaussianMeasure a) =ᵐ[equilibriumGaussianMeasure a]
      (fun x => ENNReal.ofReal (ρ x / equilibriumGaussian a x)) := by
    rw [he]
    exact Measure.rnDeriv_withDensity _ hr.ennreal_ofReal
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (ρ x / equilibriumGaussian a x))
        ∂equilibriumGaussianMeasure a := by
      apply lintegral_congr_ae
      exact hRN.mono (fun x hx => by
        dsimp only at hx ⊢
        rw [hx, ENNReal.toReal_ofReal (div_nonneg (hρ0 x) (equilibriumGaussian_pos ha x).le)])
    _ = _ := by
      unfold equilibriumGaussianMeasure equilibriumDensityMeasure
      have hkl : Measurable (fun x => ENNReal.ofReal
          (InformationTheory.klFun (ρ x / equilibriumGaussian a x))) :=
        (InformationTheory.measurable_klFun.comp hr).ennreal_ofReal
      rw [lintegral_withDensity_eq_lintegral_mul volume hγ.ennreal_ofReal hkl]
      apply lintegral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only [Pi.mul_apply]
        rw [ENNReal.ofReal_mul (equilibriumGaussian_pos ha x).le])

end RepulsiveCoulomb
