module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogMass
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Actual logarithmic potentials of bounded planar probability densities.
All integrability is proved before using real-valued integrals. These lemmas
supply the exact kernel estimates in manuscript Proposition equilibrium;
existence of the thermal minimizer is a separate outstanding construction. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The actual convolution against a planar density. -/
def equilibriumDensityPotential (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y : ℂ, equilibriumLogKernel (x - y) * ρ y

/-- Second moments suffice for logarithmic moments. -/
theorem equilibriumLogMoment_mul_integrable {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x) := by
  have hmajor := hρ2.add hρi
  apply hmajor.mono' (equilibriumLogMoment_continuous.measurable.mul hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, Pi.sub_apply, id_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (equilibriumLogMoment_nonneg x) (hρ0 x))]
    have hn : ‖x‖ ≤ ‖x‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    have hb := mul_le_mul_of_nonneg_right ((equilibriumLogMoment_le_norm x).trans hn) (hρ0 x)
    nlinarith)

/-- Bounded densities preserve local integrability of the logarithmic singularity. -/
theorem equilibriumLogPositive_mul_integrable {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumLogPositive (x - y) * ρ y) := by
  have hi := (equilibriumLogPositive_shift_integrable x).mul_const M
  apply hi.mono' ((equilibriumLogPositive_measurable.comp
    (measurable_const.sub measurable_id)).mul hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    dsimp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, Pi.sub_apply, id_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (equilibriumLogPositive_nonneg _) (hρ0 y))]
    exact mul_le_mul_of_nonneg_left (hρM y) (equilibriumLogPositive_nonneg _))

theorem integral_equilibriumLogPositive_mul_le {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (x : ℂ) :
    (∫ y : ℂ, equilibriumLogPositive (x - y) * ρ y) ≤ M * Real.pi / 2 := by
  calc
    (∫ y : ℂ, equilibriumLogPositive (x - y) * ρ y) ≤
        ∫ y : ℂ, equilibriumLogPositive (x - y) * M :=
      integral_mono (equilibriumLogPositive_mul_integrable hρm hρ0 hρM x)
        ((equilibriumLogPositive_shift_integrable x).mul_const M)
        (fun y => mul_le_mul_of_nonneg_left (hρM y) (equilibriumLogPositive_nonneg _))
    _ = M * Real.pi / 2 := by rw [integral_mul_const, integral_equilibriumLogPositive_shift]; ring

/-- Absolute integrability of the literal potential kernel at every point. -/
theorem equilibriumLogKernel_mul_integrable {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y))
    (x : ℂ) : Integrable (fun y : ℂ => equilibriumLogKernel (x - y) * ρ y) := by
  have hp := equilibriumLogPositive_mul_integrable hρm hρ0 hρM x
  have hmajor := (hp.add (hρi.const_mul (equilibriumLogMoment x))).add hρL
  apply hmajor.mono' ((equilibriumLogKernel_measurable.comp
    (measurable_const.sub measurable_id)).mul hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    dsimp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, Pi.sub_apply, id_eq]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
    have hb := mul_le_mul_of_nonneg_right (equilibriumLogKernel_abs_sub_bound x y) (hρ0 y)
    nlinarith)

/-- Exact lower potential estimate from manuscript (U-compact-lower). -/
theorem equilibriumDensityPotential_lower {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y)) (x : ℂ) :
    -equilibriumLogMoment x - (∫ y : ℂ, equilibriumLogMoment y * ρ y) ≤
      equilibriumDensityPotential ρ x := by
  have hi := (hρi.const_mul (-equilibriumLogMoment x)).sub hρL
  have hm := integral_mono hi (equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi hρL x)
    (fun y => show -equilibriumLogMoment x * ρ y - equilibriumLogMoment y * ρ y ≤
        equilibriumLogKernel (x - y) * ρ y by
      have h := mul_le_mul_of_nonneg_right (equilibriumLogKernel_sub_lower x y) (hρ0 y)
      nlinarith)
  change (∫ y : ℂ, -equilibriumLogMoment x * ρ y - equilibriumLogMoment y * ρ y) ≤
    equilibriumDensityPotential ρ x at hm
  rw [integral_sub (hρi.const_mul _) hρL, integral_const_mul, hρmass, mul_one] at hm
  exact hm

/-- The positive-kernel estimate gives a global upper bound. -/
theorem equilibriumDensityPotential_upper {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y))
    (x : ℂ) : equilibriumDensityPotential ρ x ≤ M * Real.pi / 2 := by
  apply (integral_mono (equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi hρL x)
    (equilibriumLogPositive_mul_integrable hρm hρ0 hρM x)
    (fun y => mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ0 y))).trans
  exact integral_equilibriumLogPositive_mul_le hρm hρ0 hρM x

/-- At the manuscript's density bound, the precise upper potential constant is 1/2. -/
theorem equilibriumDensityPotential_le_half {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ Real.pi⁻¹)
    (hρi : Integrable ρ) (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y))
    (x : ℂ) : equilibriumDensityPotential ρ x ≤ 1 / 2 := by
  have h := equilibriumDensityPotential_upper hρm hρ0 hρM hρi hρL x
  simpa only [inv_mul_cancel₀ Real.pi_ne_zero] using h

/-- Parameter measurability of the literal convolution. -/
theorem equilibriumDensityPotential_measurable {ρ : ℂ → ℝ} (hρm : Measurable ρ) :
    Measurable (equilibriumDensityPotential ρ) := by
  have hm : Measurable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2) * ρ p.2) :=
    (equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hρm.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end RepulsiveCoulomb
