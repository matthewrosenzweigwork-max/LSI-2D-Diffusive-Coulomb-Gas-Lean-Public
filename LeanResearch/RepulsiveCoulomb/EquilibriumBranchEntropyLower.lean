module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGaussian
public import LeanResearch.PeriodicAttractiveLogGas.Rothaus

@[expose] public section

/-! Direct entropy lower bound against the actual normalized Gaussian.
No relative entropy inequality or finite Gaussian mass is assumed. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

/-- Pointwise Gibbs inequality including zero density. -/
theorem equilibrium_mul_log_lower {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    r * Real.log s + r - s ≤ r * Real.log r := by
  have h := PeriodicAttractiveLogGas.Rothaus.log_variational_pointwise
    (A := 1) (S := 1) hr hs zero_lt_one zero_lt_one
  norm_num at h
  linarith

/-- Integrability of the Gaussian log-density against any finite second-moment density. -/
theorem equilibriumGaussian_log_mul_integrable {a : ℝ} (ha : 0 < a)
    {ρ : ℂ → ℝ} (hρi : Integrable ρ)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : ℂ => ρ x * Real.log (equilibriumGaussian a x)) := by
  have h := (hρi.const_mul (Real.log (a / Real.pi))).sub (hρ2.const_mul a)
  apply h.congr
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.sub_apply]
    rw [log_equilibriumGaussian ha]
    ring)

theorem integral_equilibriumGaussian_log_mul {a : ℝ} (ha : 0 < a)
    {ρ : ℂ → ℝ} (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    (∫ x : ℂ, ρ x * Real.log (equilibriumGaussian a x)) =
      Real.log (a / Real.pi) - a * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) := by
  have he : (fun x : ℂ => ρ x * Real.log (equilibriumGaussian a x)) =
      (fun x : ℂ => Real.log (a / Real.pi) * ρ x - a * (‖x‖ ^ 2 * ρ x)) := by
    funext x
    rw [log_equilibriumGaussian ha]
    ring
  rw [he, integral_sub (hρi.const_mul _) (hρ2.const_mul _),
    integral_const_mul, integral_const_mul, hρmass, mul_one]

/-- The actual Gaussian reference supplies entropy coercivity, with the exact
normalization log(a/pi) and all positive a allowed. -/
theorem equilibrium_entropy_lower {a : ℝ} (ha : 0 < a) {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x))) :
    Real.log (a / Real.pi) - a * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) ≤
      ∫ x : ℂ, ρ x * Real.log (ρ x) := by
  have hl := equilibriumGaussian_log_mul_integrable ha hρi hρ2
  have hg := equilibriumGaussian_integrable ha
  have hm := integral_mono ((hl.add hρi).sub hg) hρH
    (fun x => equilibrium_mul_log_lower (hρ0 x) (equilibriumGaussian_pos ha x))
  change (∫ x : ℂ, (ρ x * Real.log (equilibriumGaussian a x) + ρ x) -
      equilibriumGaussian a x) ≤ ∫ x : ℂ, ρ x * Real.log (ρ x) at hm
  have hsub := integral_sub (hl.add hρi) hg
  dsimp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hl hρi,
    integral_equilibriumGaussian_log_mul ha hρi hρmass hρ2, hρmass,
    integral_equilibriumGaussian ha] at hm
  linarith

end RepulsiveCoulomb
