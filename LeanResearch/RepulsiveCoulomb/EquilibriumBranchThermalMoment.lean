module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityScalingEnergy
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalPositivity
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! The exact manuscript second moment, obtained from actual normalized
spatial dilations and global minimality. No differentiability, radiality or
pointwise equation for the minimizing density is used in this argument. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumDensityScale_one (ρ : ℂ → ℝ) : equilibriumDensityScale 1 ρ = ρ := by
  funext x
  simp only [equilibriumDensityScale, one_pow, inv_one, one_smul, one_mul]

/-- The actual scale-parameter derivative of the physical free energy. -/
theorem equilibrium_hasDerivAt_scale_freeEnergy (β : ℝ) {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    HasDerivAt (fun t : ℝ => equilibriumDensityFreeEnergy β (equilibriumDensityScale t ρ))
      ((∫ x : ℂ, ‖x‖ ^ 2 * ρ x) - (1 / 2 + 2 / β)) 1 := by
  let m : ℝ := ∫ x : ℂ, ‖x‖ ^ 2 * ρ x
  let k : ℝ := 1 / 2 + 2 / β
  have h : HasDerivAt (fun t : ℝ => equilibriumDensityFreeEnergy β ρ +
      ((t ^ 2 - 1) * m / 2 - k * Real.log t)) (m - k) 1 := by
    have hd := ((((((hasDerivAt_id (1 : ℝ)).pow 2).sub_const 1).mul_const m).div_const 2).sub
      ((Real.hasDerivAt_log one_ne_zero).const_mul k)).const_add (equilibriumDensityFreeEnergy β ρ)
    change HasDerivAt (fun t : ℝ => equilibriumDensityFreeEnergy β ρ +
      ((t ^ 2 - 1) * m / 2 - k * Real.log t)) _ 1 at hd
    convert hd using 1 <;> norm_num <;> ring
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
  change (0 : ℝ) < t at ht
  have he := equilibriumDensityScale_freeEnergy (β := β) ht hρ0 hρi hρmass hρH hG
  dsimp only [m, k]
  linarith

/-- Every finite-energy canonical minimizing density has the exact moment.
All nearby scaled densities are verified admissible before using minimality. -/
theorem equilibriumDensityMinimizer_secondMoment {β : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤ equilibriumCanonicalFreeEnergy β ν) :
    (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) = 1 / 2 + 2 / β := by
  let F : ℝ → ℝ := fun t => equilibriumDensityFreeEnergy β (equilibriumDensityScale t ρ)
  have hlocal : IsLocalMin F 1 := by
    change ∀ᶠ t in 𝓝 (1 : ℝ), F 1 ≤ F t
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    change (0 : ℝ) < t at ht
    let ψ := equilibriumDensityScale t ρ
    have hψm : Measurable ψ := equilibriumDensityScale_measurable t hρm
    have hψ0 : ∀ x, 0 ≤ ψ x := equilibriumDensityScale_nonneg t hρ0
    have hψi : Integrable ψ := equilibriumDensityScale_integrable ht hρi
    have hψmass : (∫ x : ℂ, ψ x) = 1 := by rw [integral_equilibriumDensityScale ht, hρmass]
    have hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x) := equilibriumDensityScale_secondMoment_integrable ht hρ2
    have hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)) := equilibriumDensityScale_entropy_integrable ht hρ0 hρi hρH
    have hψG := equilibriumDensityScale_logEnergy_integrable ht hρi hG
    letI := equilibriumDensityMeasure_probability hψ0 hψi hψmass
    let ν : ProbabilityMeasure ℂ := ⟨equilibriumDensityMeasure ψ, inferInstance⟩
    have hc := hmin ν
    change equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ψ) at hc
    rw [equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hρm hρ0 hρi hρmass hρ2 hρH hG,
      equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hψm hψ0 hψi hψmass hψ2 hψH hψG] at hc
    dsimp only [F]
    rw [equilibriumDensityScale_one]
    exact EReal.coe_le_coe_iff.mp hc
  have hd := equilibrium_hasDerivAt_scale_freeEnergy β hρ0 hρi hρmass hρH hG
  exact sub_eq_zero.mp (hlocal.hasDerivAt_eq_zero hd)

/-- Actual finite-objective thermal minimizers have the manuscript's exact
normalization for every positive beta, without regularity assumptions. -/
theorem equilibriumCanonicalMinimizer_secondMoment {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hfinite : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) = 1 / 2 + 2 / β := by
  let ρ := equilibriumReferenceDensity μ
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hfinite
  have hP2 := equilibriumObjective_finite_secondMoment hfinite
  have hρm : Measurable ρ := equilibriumReferenceDensity_measurable μ
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumReferenceDensity_nonneg μ
  have hρi : Integrable ρ := equilibriumReferenceDensity_integrable μ
  have hρmass : (∫ x : ℂ, ρ x) = 1 := integral_equilibriumReferenceDensity hAC
  have hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hAC hP2
  have hρH := equilibriumObjective_finite_entropy_integrable hβ hfinite
  have hρmeasure : equilibriumDensityMeasure ρ = (μ : Measure ℂ) := equilibriumReferenceDensity_measure hAC
  have hρGμ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) := by
    rw [hρmeasure]
    exact equilibriumObjective_finite_logEnergy_integrable hβ hfinite
  have hG := equilibriumDensityMeasure_energy_to_density hρm hρ0 hρGμ
  have hminρ : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤ equilibriumCanonicalFreeEnergy β ν := by
    intro ν
    rw [hρmeasure]
    exact hmin ν
  have hm := equilibriumDensityMinimizer_secondMoment hβ hρm hρ0 hρi hρmass hρ2 hρH hG hminρ
  rw [integral_equilibriumReferenceDensity_secondMoment hAC] at hm
  exact hm

end RepulsiveCoulomb
