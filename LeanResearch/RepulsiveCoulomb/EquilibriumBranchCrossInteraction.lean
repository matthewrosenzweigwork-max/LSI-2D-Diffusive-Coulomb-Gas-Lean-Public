import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPotential
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual absolute integrability of cross Coulomb interactions and signed
density differences. This discharges the natural finite-energy hypotheses
needed when applying logarithmic repulsivity to bounded probability densities. -/
noncomputable section
open MeasureTheory Real Filter
namespace RepulsiveCoulomb

private theorem equilibriumKernel_norm_integral_bound {σ : ℂ → ℝ} {M : ℝ}
    (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσM : ∀ x, σ x ≤ M)
    (hσi : Integrable σ) (hσmass : (∫ x : ℂ, σ x) = 1)
    (hσL : Integrable (fun x : ℂ => equilibriumLogMoment x * σ x)) (x : ℂ) :
    (∫ y : ℂ, ‖equilibriumLogKernel (x - y) * σ y‖) ≤
      M * Real.pi / 2 + equilibriumLogMoment x + (∫ y : ℂ, equilibriumLogMoment y * σ y) := by
  have hk := equilibriumLogKernel_mul_integrable hσm hσ0 hσM hσi hσL x
  have hp := equilibriumLogPositive_mul_integrable hσm hσ0 hσM x
  have hi := (hp.add (hσi.const_mul (equilibriumLogMoment x))).add hσL
  have hm := integral_mono hk.norm hi (fun y => by
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσ0 y)]
    have h := mul_le_mul_of_nonneg_right (equilibriumLogKernel_abs_sub_bound x y) (hσ0 y)
    nlinarith)
  change (∫ y : ℂ, ‖equilibriumLogKernel (x - y) * σ y‖) ≤
      ∫ y : ℂ, (equilibriumLogPositive (x - y) * σ y + equilibriumLogMoment x * σ y) +
        equilibriumLogMoment y * σ y at hm
  have h₁ := integral_add (hp.add (hσi.const_mul (equilibriumLogMoment x))) hσL
  have h₂ := integral_add hp (hσi.const_mul (equilibriumLogMoment x))
  dsimp only [Pi.add_apply] at h₁ h₂
  rw [h₁, h₂, integral_const_mul, hσmass, mul_one] at hm
  have hu := integral_equilibriumLogPositive_mul_le hσm hσ0 hσM x
  linarith

/-- Every cross interaction of bounded probability densities with finite
logarithmic moments is an actual absolutely integrable product-space function. -/
theorem equilibriumCrossInteraction_integrable {ρ σ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρL : Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x))
    (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσM : ∀ x, σ x ≤ M)
    (hσi : Integrable σ) (hσmass : (∫ x : ℂ, σ x) = 1)
    (hσL : Integrable (fun x : ℂ => equilibriumLogMoment x * σ x)) :
    Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * σ p.2)) (volume.prod volume) := by
  let G : ℂ × ℂ → ℝ := fun p => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * σ p.2)
  have hGm : Measurable G :=
    (hρm.comp measurable_fst).mul
      ((equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
        (hσm.comp measurable_snd))
  have hGs (x : ℂ) : Integrable (fun y : ℂ => G (x, y)) :=
    (equilibriumLogKernel_mul_integrable hσm hσ0 hσM hσi hσL x).const_mul (ρ x)
  have hmajor := (hρi.const_mul (M * Real.pi / 2 +
    (∫ y : ℂ, equilibriumLogMoment y * σ y))).add hρL
  have hnorm : Integrable (fun x : ℂ => ∫ y : ℂ, ‖G (x, y)‖) := by
    apply hmajor.mono' hGm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
      have he : (fun y : ℂ => ‖G (x, y)‖) =
          (fun y : ℂ => ρ x * ‖equilibriumLogKernel (x - y) * σ y‖) := by
        funext y
        dsimp only [G]
        rw [norm_mul, Real.norm_eq_abs (ρ x), abs_of_nonneg (hρ0 x)]
      rw [he, integral_const_mul]
      have h := mul_le_mul_of_nonneg_left
        (equilibriumKernel_norm_integral_bound hσm hσ0 hσM hσi hσmass hσL x) (hρ0 x)
      nlinarith)
  exact (integrable_prod_iff hGm.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall hGs, hnorm⟩

/-- The difference of two bounded probability densities has finite absolute
Coulomb energy, proved by the four actual cross-interaction integrals. -/
theorem equilibriumDifference_logEnergy_integrable {ρ σ : ℂ → ℝ} {Mρ Mσ : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ Mρ)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρL : Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x))
    (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσM : ∀ x, σ x ≤ Mσ)
    (hσi : Integrable σ) (hσmass : (∫ x : ℂ, σ x) = 1)
    (hσL : Integrable (fun x : ℂ => equilibriumLogMoment x * σ x)) :
    Integrable (fun p : ℂ × ℂ => (ρ p.1 - σ p.1) * (ρ p.2 - σ p.2) *
      equilibriumLogKernel (p.1 - p.2)) (volume.prod volume) := by
  have hrr := equilibriumCrossInteraction_integrable hρm hρ0 hρi hρL
    hρm hρ0 hρM hρi hρmass hρL
  have hrs := equilibriumCrossInteraction_integrable hρm hρ0 hρi hρL
    hσm hσ0 hσM hσi hσmass hσL
  have hsr := equilibriumCrossInteraction_integrable hσm hσ0 hσi hσL
    hρm hρ0 hρM hρi hρmass hρL
  have hss := equilibriumCrossInteraction_integrable hσm hσ0 hσi hσL
    hσm hσ0 hσM hσi hσmass hσL
  apply (((hrr.sub hrs).sub hsr).add hss).congr
  exact Eventually.of_forall (fun p => by
    dsimp only [Pi.sub_apply, Pi.add_apply]
    ring)

end RepulsiveCoulomb
