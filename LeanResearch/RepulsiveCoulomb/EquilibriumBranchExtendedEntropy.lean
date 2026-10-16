module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityMeasure
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyNegative
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedIntegral

@[expose] public section

/-! Exact Gaussian entropy correspondence on the entire P2 density domain,
including infinite positive entropy. The normalized Gaussian and its RN
identification are actual constructions, not assumed entropy data. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Pointwise Gaussian KL identity, including zero density. -/
theorem equilibriumGaussian_klFun_identity {a : ℝ} (ha : 0 < a)
    {r : ℝ} (hr : 0 ≤ r) (x : ℂ) :
    equilibriumGaussian a x * InformationTheory.klFun (r / equilibriumGaussian a x) =
      r * Real.log r + a * (‖x‖ ^ 2 * r) + equilibriumGaussian a x -
        (1 + Real.log (a / Real.pi)) * r := by
  by_cases hr0 : r = 0
  · subst r
    simp only [zero_div, InformationTheory.klFun_zero, mul_one, zero_mul, mul_zero,
      add_zero, zero_add, sub_zero]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [InformationTheory.klFun, Real.log_div hr0 (equilibriumGaussian_pos ha x).ne',
    log_equilibriumGaussian ha]
  field_simp [(equilibriumGaussian_pos ha x).ne'] <;> ring

/-- The full extended entropy identity on P2. The positive entropy may be
infinite; its negative part is proved integrable before the shift identity is
used. The Gaussian normalization contributes exactly log(a/pi). -/
theorem equilibriumExtendedEntropy_eq_gaussian_klDiv {a : ℝ} (ha : 0 < a)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    equilibriumExtendedIntegral volume (fun x : ℂ => ρ x * Real.log (ρ x)) =
      (InformationTheory.klDiv (equilibriumDensityMeasure ρ) (equilibriumGaussianMeasure a) : EReal) -
        (a * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) - Real.log (a / Real.pi) : ℝ) := by
  let k : ℂ → ℝ := fun x => a * (‖x‖ ^ 2 * ρ x) + equilibriumGaussian a x -
    (1 + Real.log (a / Real.pi)) * ρ x
  have hk : Integrable k := ((hρ2.const_mul a).add (equilibriumGaussian_integrable ha)).sub
    (hρi.const_mul (1 + Real.log (a / Real.pi)))
  have hki : (∫ x : ℂ, k x) =
      a * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) - Real.log (a / Real.pi) := by
    unfold k
    have hsub := integral_sub ((hρ2.const_mul a).add (equilibriumGaussian_integrable ha))
      (hρi.const_mul (1 + Real.log (a / Real.pi)))
    dsimp only [Pi.add_apply] at hsub
    rw [hsub, integral_add (hρ2.const_mul a) (equilibriumGaussian_integrable ha),
      integral_const_mul, integral_const_mul, integral_equilibriumGaussian ha, hρmass, mul_one]
    ring
  have hid (x : ℂ) : ρ x * Real.log (ρ x) + k x =
      equilibriumGaussian a x * InformationTheory.klFun (ρ x / equilibriumGaussian a x) := by
    rw [equilibriumGaussian_klFun_identity ha (hρ0 x) x]
    dsimp only [k]
    ring
  have hn (x : ℂ) : 0 ≤ ρ x * Real.log (ρ x) + k x := by
    rw [hid]
    exact mul_nonneg (equilibriumGaussian_pos ha x).le
      (InformationTheory.klFun_nonneg (div_nonneg (hρ0 x) (equilibriumGaussian_pos ha x).le))
  have he := equilibriumExtendedIntegral_eq_shifted
    (hρm.mul (Real.measurable_log.comp hρm))
    (equilibriumEntropyNegative_integrable ha hρm hρ0 hρi hρ2) hk hn
  have hkl : (∫⁻ x : ℂ, ENNReal.ofReal (ρ x * Real.log (ρ x) + k x)) =
      InformationTheory.klDiv (equilibriumDensityMeasure ρ) (equilibriumGaussianMeasure a) := by
    rw [equilibriumGaussian_klDiv_density ha hρm hρ0 hρi hρmass]
    apply lintegral_congr_ae
    exact Eventually.of_forall (fun x => congrArg ENNReal.ofReal (hid x))
  dsimp only [Pi.mul_apply, Function.comp_apply] at he
  rw [hkl, hki] at he
  exact he

end RepulsiveCoulomb
