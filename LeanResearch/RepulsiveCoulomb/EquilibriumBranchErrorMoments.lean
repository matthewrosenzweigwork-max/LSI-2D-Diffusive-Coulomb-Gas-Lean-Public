import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircularRegularization
import Mathlib.Analysis.Complex.Exponential

/-! All integer moment bounds for the literal circular regularization error.
The epsilon-squared rate and factorial dependence are explicit and are uniform
in translations and in any density bounded by M. These are analytic inputs
to, rather than a substitute for, the repulsive partition argument. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- A single existing inverse-distance majorant controls every positive
integer power of the positive logarithm. -/
theorem equilibriumLogPositive_pow_le_force (p : ℕ) (hp : 0 < p) (z : ℂ) :
    equilibriumLogPositive z ^ p ≤ (p.factorial : ℝ) * truncatedLogKernel 1 z := by
  by_cases hz : z = 0
  · subst z
    simp [equilibriumLogPositive, equilibriumLogKernel, truncatedLogKernel, hp.ne']
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases h1 : ‖z‖ < 1
  · have hl : 0 ≤ -Real.log ‖z‖ := neg_nonneg.mpr (Real.log_neg hn h1).le
    have h := Real.pow_div_factorial_le_exp (-Real.log ‖z‖) hl p
    have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    rw [div_le_iff₀ hf, Real.exp_neg, Real.exp_log hn] at h
    simpa only [equilibriumLogPositive, equilibriumLogKernel, max_eq_left hl,
      truncatedLogKernel, if_pos h1, mul_comm] using h
  · have hl := Real.log_nonneg (le_of_not_gt h1)
    simp [equilibriumLogPositive, equilibriumLogKernel, max_eq_right (neg_nonpos.mpr hl),
      truncatedLogKernel, h1, hp.ne']

theorem equilibriumLogPositive_pow_integrable (p : ℕ) (hp : 0 < p) :
    Integrable (fun z : ℂ => equilibriumLogPositive z ^ p) := by
  apply ((truncatedLogKernel_integrable 1).const_mul (p.factorial : ℝ)).mono'
    (equilibriumLogPositive_measurable.pow_const p).aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (equilibriumLogPositive_nonneg z) p)]
    exact equilibriumLogPositive_pow_le_force p hp z)

theorem integral_equilibriumLogPositive_pow_le (p : ℕ) (hp : 0 < p) :
    (∫ z : ℂ, equilibriumLogPositive z ^ p) ≤ 2 * Real.pi * (p.factorial : ℝ) := by
  have hm := integral_mono (equilibriumLogPositive_pow_integrable p hp)
    ((truncatedLogKernel_integrable 1).const_mul (p.factorial : ℝ))
    (equilibriumLogPositive_pow_le_force p hp)
  rw [integral_const_mul, integral_truncatedLogKernel (by norm_num : (0 : ℝ) ≤ 1)] at hm
  nlinarith

theorem equilibriumCircularError_pow_integrable {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) : Integrable (fun z : ℂ => equilibriumCircularError ε z ^ p) :=
  (equilibriumLogPositive_pow_integrable p hp).comp_smul (inv_ne_zero hε.ne')

/-- The all-integer-p Besov-type error rate used by the partition construction. -/
theorem integral_equilibriumCircularError_pow_le {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) :
    (∫ z : ℂ, equilibriumCircularError ε z ^ p) ≤
      2 * Real.pi * (p.factorial : ℝ) * ε ^ 2 := by
  unfold equilibriumCircularError
  rw [Measure.integral_comp_inv_smul (volume : Measure ℂ)
    (fun z : ℂ => equilibriumLogPositive z ^ p) ε]
  simp only [Complex.finrank_real_complex, smul_eq_mul, abs_of_nonneg (sq_nonneg ε)]
  have h := mul_le_mul_of_nonneg_left (integral_equilibriumLogPositive_pow_le p hp) (sq_nonneg ε)
  nlinarith

/-- Translation does not change the quantitative error moment bound. -/
theorem integral_equilibriumCircularError_pow_shift_le {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (x : ℂ) :
    (∫ y : ℂ, equilibriumCircularError ε (y - x) ^ p) ≤
      2 * Real.pi * (p.factorial : ℝ) * ε ^ 2 := by
  rw [integral_sub_right_eq_self (fun y : ℂ => equilibriumCircularError ε y ^ p) x]
  exact integral_equilibriumCircularError_pow_le hε p hp

/-- Every density bounded by M obeys the same small-scale moment bound;
normalization or a moment hypothesis is unnecessary for this local estimate. -/
theorem equilibriumCircularError_pow_mul_integrable {ε M : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumCircularError ε (y - x) ^ p * ρ y) := by
  have hi := ((equilibriumCircularError_pow_integrable hε p hp).comp_sub_right x).mul_const M
  apply hi.mono' (((equilibriumCircularError_measurable ε).comp
    (measurable_id.sub measurable_const)).pow_const p |>.mul hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    dsimp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply, id_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pow_nonneg (equilibriumCircularError_nonneg ε _) p) (hρ0 y))]
    exact mul_le_mul_of_nonneg_left (hρM y)
      (pow_nonneg (equilibriumCircularError_nonneg ε _) p))

theorem integral_equilibriumCircularError_pow_mul_le {ε M : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M) (x : ℂ) :
    (∫ y : ℂ, equilibriumCircularError ε (y - x) ^ p * ρ y) ≤
      2 * Real.pi * (p.factorial : ℝ) * ε ^ 2 * M := by
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  calc
    _ ≤ ∫ y : ℂ, equilibriumCircularError ε (y - x) ^ p * M :=
      integral_mono (equilibriumCircularError_pow_mul_integrable hε p hp hρm hρ0 hρM x)
        (((equilibriumCircularError_pow_integrable hε p hp).comp_sub_right x).mul_const M)
        (fun y => mul_le_mul_of_nonneg_left (hρM y)
          (pow_nonneg (equilibriumCircularError_nonneg ε _) p))
    _ ≤ _ := by
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right
        (integral_equilibriumCircularError_pow_shift_le hε p hp x) hM

end RepulsiveCoulomb
