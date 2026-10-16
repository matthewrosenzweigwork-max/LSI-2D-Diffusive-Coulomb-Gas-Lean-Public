module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchELUniqueness
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

/-! Actual radiality of positive bounded pointwise-EL densities. Orthogonal
pullbacks preserve planar volume and the literal logarithmic potential.
The preceding EL uniqueness gives a.e. invariance, then the pointwise EL
identity and everywhere equality of potentials give pointwise invariance.
No continuity or radiality is assumed. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

/-- Exact covariance of the literal potential under any real linear isometry. -/
theorem equilibriumDensityPotential_comp_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ) (ρ : ℂ → ℝ) (x : ℂ) :
    equilibriumDensityPotential (ρ ∘ e) x = equilibriumDensityPotential ρ (e x) := by
  have hg (y : ℂ) : equilibriumLogKernel (e x - e y) = equilibriumLogKernel (x - y) := by
    rw [← map_sub]
    simp only [equilibriumLogKernel, e.norm_map]
  unfold equilibriumDensityPotential
  calc
    (∫ y : ℂ, equilibriumLogKernel (x - y) * (ρ ∘ e) y) =
        ∫ y : ℂ, equilibriumLogKernel (e x - e y) * ρ (e y) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by simp only [Function.comp_apply, hg])
    _ = ∫ y : ℂ, equilibriumLogKernel (e x - y) * ρ y :=
      e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
        (fun y : ℂ => equilibriumLogKernel (e x - y) * ρ y)

/-- EL uniqueness yields pointwise orthogonal invariance, even before a
continuity theorem for the potential has been established. -/
theorem equilibrium_pointwise_EL_isometry_invariant {β C M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρL : Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x))
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (e : ℂ ≃ₗᵢ[ℝ] ℂ) (x : ℂ) : ρ (e x) = ρ x := by
  let σ : ℂ → ℝ := ρ ∘ e
  have hσm : Measurable σ := hρm.comp e.continuous.measurable
  have hσpos : ∀ y, 0 < σ y := fun y => hρpos (e y)
  have hσM : ∀ y, σ y ≤ M := fun y => hρM (e y)
  have hσi : Integrable σ := e.measurePreserving.integrable_comp_of_integrable hρi
  have hσmass : (∫ y : ℂ, σ y) = 1 := by
    rw [show (∫ y : ℂ, σ y) = ∫ y : ℂ, ρ y from
      e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding ρ]
    exact hρmass
  have hσL : Integrable (fun y : ℂ => equilibriumLogMoment y * σ y) := by
    have h := e.measurePreserving.integrable_comp_of_integrable hρL
    simpa only [Function.comp_def, equilibriumLogMoment, e.norm_map, σ] using h
  have hσEL (y : ℂ) : Real.log (σ y) =
      -β * (‖y‖ ^ 2 / 2 + equilibriumDensityPotential σ y) + C := by
    change Real.log (ρ (e y)) = -β * (‖y‖ ^ 2 / 2 + equilibriumDensityPotential (ρ ∘ e) y) + C
    rw [equilibriumDensityPotential_comp_isometry]
    simpa only [e.norm_map] using hEL (e y)
  have heq : σ =ᵐ[volume] ρ := equilibrium_pointwise_EL_densities_unique hβ
    hσm hσpos hσM hσi hσmass hσL hρm hρpos hρM hρi hρmass hρL hσEL hEL
  apply Real.log_injOn_pos (hρpos (e x)) (hρpos x)
  change Real.log (σ x) = Real.log (ρ x)
  rw [hσEL x, hEL x, equilibriumDensityPotential_congr_ae heq x]

/-- The literal representative depends only on the radius. -/
theorem equilibrium_pointwise_EL_radial {β C M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρL : Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x))
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    {x y : ℂ} (hxy : ‖x‖ = ‖y‖) : ρ x = ρ y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by simpa only [hx, norm_zero] using hxy.symm)
    rw [hx, hy]
  · let u : Circle := ⟨y / x, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_div, ← hxy, div_self (norm_ne_zero_iff.mpr hx)]⟩
    have hu : rotation u x = y := by
      change (y / x) * x = y
      exact div_mul_cancel₀ y hx
    have h := equilibrium_pointwise_EL_isometry_invariant hβ hρm hρpos hρM hρi hρmass hρL hEL (rotation u) x
    rw [hu] at h
    exact h.symm

end RepulsiveCoulomb
