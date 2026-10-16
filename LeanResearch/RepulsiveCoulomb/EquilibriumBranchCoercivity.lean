import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyLower

/-! Explicit manuscript free-energy coercivity on bounded finite-energy
probability densities. Extended-energy weak compactness and attainment are
separate obligations; no minimizer is asserted in this module. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

/-- The manuscript's real free energy, to be used only after the three
integrability obligations have been established. -/
def equilibriumDensityFreeEnergy (β : ℝ) (ρ : ℂ → ℝ) : ℝ :=
  (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) / 2 + equilibriumDensityInteraction ρ / 2 +
    (∫ x : ℂ, ρ x * Real.log (ρ x)) / β

/-- The explicit quarter-moment coercive bound, with no temperature restriction
beyond beta>0. This is on the finite bounded-density domain. -/
theorem equilibriumDensityFreeEnergy_coercive {β M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρM : ∀ x, ρ x ≤ M) (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x))) :
    (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) / 4 - 2 + Real.log (β / (8 * Real.pi)) / β ≤
      equilibriumDensityFreeEnergy β ρ := by
  have hL := equilibriumLogMoment_integral_le_quadratic
    (by norm_num : (0 : ℝ) < 1 / 8) hρm hρ0 hρi hρmass hρ2
  have hc := equilibriumDensityInteraction_lower hρm hρ0 hρM hρi hρmass
    (equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2)
  have he := equilibrium_entropy_lower (by positivity : 0 < β / 8)
    hρ0 hρi hρmass hρ2 hρH
  have he' := div_le_div_of_nonneg_right he hβ.le
  have hid : (β / 8) / Real.pi = β / (8 * Real.pi) := by
    field_simp
  rw [hid] at he'
  have hexpand : (Real.log (β / (8 * Real.pi)) -
      (β / 8) * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x)) / β =
      Real.log (β / (8 * Real.pi)) / β - (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) / 8 := by
    field_simp [hβ.ne']
  rw [hexpand] at he'
  norm_num at hL
  unfold equilibriumDensityFreeEnergy
  linarith

end RepulsiveCoulomb
