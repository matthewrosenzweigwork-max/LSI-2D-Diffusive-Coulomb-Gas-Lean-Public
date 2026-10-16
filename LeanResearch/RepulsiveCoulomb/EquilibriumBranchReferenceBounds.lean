module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPolynomialGaussian

@[expose] public section

/-! Exact reference-potential and normalization bounds for the actually
constructed equilibrium. The sharp cap gives U<=1/2, and the exact second
moment controls the logarithmic moment uniformly above a positive beta floor.
No continuity in the temperature parameter is required. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumCompactLogBound (βlo : ℝ) : ℝ := 3 / 4 + 2 / βlo

theorem equilibriumReference_logMoment_integrable {β : ℝ} (R : EquilibriumConstructedReference β) :
    Integrable (fun x : ℂ => equilibriumLogMoment x * R.density x) :=
  equilibriumLogMoment_mul_integrable R.smooth.continuous.measurable
    (fun x => (R.positive x).le) R.integrable R.secondMoment_integrable

theorem equilibriumReference_potential_upper {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) :
    equilibriumDensityPotential R.density x ≤ 1 / 2 :=
  equilibriumDensityPotential_le_half R.smooth.continuous.measurable (fun y => (R.positive y).le)
    R.cap R.integrable (equilibriumReference_logMoment_integrable R) x

theorem equilibriumReference_potential_lower {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) :
    -equilibriumLogMoment x - (∫ y : ℂ, equilibriumLogMoment y * R.density y) ≤
      equilibriumDensityPotential R.density x :=
  equilibriumDensityPotential_lower R.smooth.continuous.measurable (fun y => (R.positive y).le)
    R.cap R.integrable R.mass_one (equilibriumReference_logMoment_integrable R) x

/-- The exact moment yields a uniform logarithmic moment on every compact
positive-temperature interval, without a parameter regularity hypothesis. -/
theorem equilibriumReference_logMoment_bound {β βlo : ℝ} (hlo : 0 < βlo) (hβlo : βlo ≤ β)
    (R : EquilibriumConstructedReference β) :
    (∫ x : ℂ, equilibriumLogMoment x * R.density x) ≤ equilibriumCompactLogBound βlo := by
  have h := equilibriumLogMoment_integral_le_quadratic (δ := 1) zero_lt_one
    R.smooth.continuous.measurable (fun x => (R.positive x).le) R.integrable R.mass_one R.secondMoment_integrable
  rw [R.secondMoment] at h
  norm_num at h
  have hdiv : 2 / β ≤ 2 / βlo := div_le_div_of_nonneg_left (by norm_num) hlo hβlo
  unfold equilibriumCompactLogBound
  linarith

/-- Integrating the pointwise EL lower Gaussian gives the exact upper bound
on exp(C_beta). The normalization beta/(2*pi) is not absorbed into a constant. -/
theorem equilibriumReference_exp_elConstant_le {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    Real.exp R.elConstant ≤ (β / (2 * Real.pi)) * Real.exp (β / 2) := by
  let K : ℝ := Real.exp (R.elConstant - β / 2) * (2 * Real.pi / β)
  have ha : 0 < β / 2 := half_pos hβ
  have hlower (x : ℂ) : K * equilibriumGaussian (β / 2) x ≤ R.density x := by
    have he : K * equilibriumGaussian (β / 2) x =
        Real.exp (R.elConstant - β / 2 - β * ‖x‖ ^ 2 / 2) := by
      have hexp : Real.exp (R.elConstant - β / 2) * Real.exp (-(β / 2) * ‖x‖ ^ 2) =
          Real.exp (R.elConstant - β / 2 - β * ‖x‖ ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      unfold K equilibriumGaussian
      field_simp [hβ.ne', Real.pi_ne_zero] <;> ring
    rw [he, equilibrium_pointwise_EL_density_eq_exp R.positive R.eulerLagrange x]
    apply Real.exp_le_exp.mpr
    have hu := mul_le_mul_of_nonneg_left (equilibriumReference_potential_upper R x) hβ.le
    nlinarith
  have hK := integral_mono ((equilibriumGaussian_integrable ha).const_mul K) R.integrable hlower
  rw [integral_const_mul, integral_equilibriumGaussian ha, R.mass_one, mul_one] at hK
  dsimp only [K] at hK
  rw [Real.exp_sub] at hK
  have hp : 0 ≤ (β / (2 * Real.pi)) * Real.exp (β / 2) := by positivity
  have hm := mul_le_mul_of_nonneg_right hK hp
  convert hm using 1 <;> field_simp [hβ.ne', Real.pi_ne_zero, Real.exp_ne_zero (β / 2)] <;> ring

/-- Actual interaction constants are bounded uniformly above any positive
temperature floor, with the manuscript upper potential constant one-half. -/
theorem equilibriumReference_interaction_abs_bound {β βlo : ℝ} (hlo : 0 < βlo) (hβlo : βlo ≤ β)
    (R : EquilibriumConstructedReference β) :
    |equilibriumDensityInteraction R.density| ≤ 2 * equilibriumCompactLogBound βlo + 1 / 2 := by
  have hρm := R.smooth.continuous.measurable
  have hρ0 := fun x => (R.positive x).le
  have hL := equilibriumReference_logMoment_integrable R
  have hl := equilibriumDensityInteraction_lower hρm hρ0 R.cap R.integrable R.mass_one hL
  have hu := equilibriumDensityInteraction_upper hρm hρ0 R.cap R.integrable R.mass_one hL
  simp only [inv_mul_cancel₀ Real.pi_ne_zero] at hu
  have hbound := equilibriumReference_logMoment_bound hlo hβlo R
  have hL0 : (0 : ℝ) ≤ ∫ x : ℂ, equilibriumLogMoment x * R.density x :=
    integral_nonneg (fun x => mul_nonneg (equilibriumLogMoment_nonneg x) (hρ0 x))
  apply abs_le.mpr
  constructor <;> linarith

end RepulsiveCoulomb
