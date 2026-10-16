module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchInteraction
public import LeanResearch.RepulsiveCoulomb.WeightedPointNormalization
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-! A genuine finite-free-energy Gaussian competitor for every positive
confinement parameter. This is the first direct-method existence input,
not an assumed probability measure or assumed finite interaction integral. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

/-- The normalized planar Gaussian used in the equilibrium entropy bound. -/
def equilibriumGaussian (a : ℝ) (x : ℂ) : ℝ :=
  (a / Real.pi) * Real.exp (-a * ‖x‖ ^ 2)

theorem equilibriumGaussian_continuous (a : ℝ) : Continuous (equilibriumGaussian a) := by
  unfold equilibriumGaussian
  fun_prop

theorem equilibriumGaussian_pos {a : ℝ} (ha : 0 < a) (x : ℂ) :
    0 < equilibriumGaussian a x := mul_pos (div_pos ha Real.pi_pos) (Real.exp_pos _)

theorem equilibriumGaussian_le {a : ℝ} (ha : 0 < a) (x : ℂ) :
    equilibriumGaussian a x ≤ a / Real.pi := by
  have he : Real.exp (-a * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg _))
  simpa only [equilibriumGaussian, mul_one] using
    mul_le_mul_of_nonneg_left he (div_nonneg ha.le Real.pi_pos.le)

theorem equilibriumGaussian_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (equilibriumGaussian a) := (integrable_planar_gaussian ha).const_mul _

theorem integral_equilibriumGaussian {a : ℝ} (ha : 0 < a) :
    (∫ x : ℂ, equilibriumGaussian a x) = 1 := by
  unfold equilibriumGaussian
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ha]
  simp only [Complex.finrank_real_complex]
  norm_num <;> field_simp [ha.ne', Real.pi_ne_zero]

/-- Finite second moment, proved by domination by a wider Gaussian. -/
theorem equilibriumGaussian_secondMoment_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumGaussian a x) := by
  have hi := (integrable_planar_gaussian (half_pos ha)).const_mul (2 / Real.pi)
  apply hi.mono' (by unfold equilibriumGaussian; fun_prop)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (equilibriumGaussian_pos ha x).le)]
    have h := Real.add_one_le_exp ((a / 2) * ‖x‖ ^ 2)
    have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-a * ‖x‖ ^ 2)).le
    rw [← Real.exp_add] at hm
    have hexp : (a / 2) * ‖x‖ ^ 2 + (-a * ‖x‖ ^ 2) = -(a / 2) * ‖x‖ ^ 2 := by ring
    rw [hexp] at hm
    have hp := Real.exp_pos (-a * ‖x‖ ^ 2)
    have hn : a * ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) ≤
        2 * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by nlinarith
    unfold equilibriumGaussian
    convert div_le_div_of_nonneg_right hn Real.pi_pos.le using 1 <;> ring)

theorem log_equilibriumGaussian {a : ℝ} (ha : 0 < a) (x : ℂ) :
    Real.log (equilibriumGaussian a x) = Real.log (a / Real.pi) - a * ‖x‖ ^ 2 := by
  rw [equilibriumGaussian, Real.log_mul (div_ne_zero ha.ne' Real.pi_ne_zero)
    (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem equilibriumGaussian_entropy_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℂ => equilibriumGaussian a x * Real.log (equilibriumGaussian a x)) := by
  have h := ((equilibriumGaussian_integrable ha).const_mul (Real.log (a / Real.pi))).sub
    ((equilibriumGaussian_secondMoment_integrable ha).const_mul a)
  apply h.congr
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.sub_apply]
    rw [log_equilibriumGaussian ha]
    ring)

/-- The Gaussian competitor has actual finite logarithmic interaction. -/
theorem equilibriumGaussian_interaction_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℂ => equilibriumDensityPotential (equilibriumGaussian a) x *
      equilibriumGaussian a x) := by
  have hm := (equilibriumGaussian_continuous a).measurable
  have h0 := fun x => (equilibriumGaussian_pos ha x).le
  have hi := equilibriumGaussian_integrable ha
  exact equilibriumDensityInteraction_integrable hm h0 (equilibriumGaussian_le ha)
    hi (integral_equilibriumGaussian ha)
    (equilibriumLogMoment_mul_integrable hm h0 hi (equilibriumGaussian_secondMoment_integrable ha))

end RepulsiveCoulomb
