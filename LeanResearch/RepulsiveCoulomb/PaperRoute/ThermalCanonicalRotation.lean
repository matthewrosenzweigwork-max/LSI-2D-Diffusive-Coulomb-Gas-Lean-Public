import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalUniqueness
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Literal canonical-energy invariance under
real linear isometries, followed by measure invariance from the NEW Green/
strict-entropy uniqueness theorem. No old EL radiality, old uniqueness or
constructed thermal reference is used. No assertion is made that an arbitrary
RN density representative is pointwise radial. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Exact law of the transported density, using physical planar volume. -/
theorem thermalDensityMeasure_map_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) :
    Measure.map e (equilibriumDensityMeasure ρ) =
      equilibriumDensityMeasure (ρ ∘ e.symm) := by
  unfold equilibriumDensityMeasure
  ext A hA
  rw [Measure.map_apply e.continuous.measurable hA,
    withDensity_apply _ (e.continuous.measurable hA), withDensity_apply _ hA]
  have h := e.measurePreserving.setLIntegral_comp_preimage hA
    ((hρm.comp e.symm.continuous.measurable).ennreal_ofReal)
  simpa only [Function.comp_def, e.symm_apply_apply] using h

theorem thermalDensityLogIntegrand_comp_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ)
    (ρ : ℂ → ℝ) :
    thermalDensityLogIntegrand (ρ ∘ e) =
      thermalDensityLogIntegrand ρ ∘ Prod.map e e := by
  funext p
  have hn : ‖e p.1-e p.2‖ = ‖p.1-p.2‖ := by
    simpa only [dist_eq_norm] using e.dist_map p.1 p.2
  simp only [thermalDensityLogIntegrand, equilibriumLogKernel,
    Function.comp_def, Prod.map_fst, Prod.map_snd, hn]

/-- Both integrability and the exact actual product-energy equality are
transported, not inferred from a totalized real integral. -/
theorem thermalDensityLogEnergy_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ)
    {ρ : ℂ → ℝ}
    (hG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) :
    Integrable (thermalDensityLogIntegrand (ρ ∘ e)) (volume.prod volume) ∧
      thermalDensityLogEnergy (ρ ∘ e) = thermalDensityLogEnergy ρ := by
  have he := e.measurePreserving.prod e.measurePreserving
  have hemb := e.toHomeomorph.measurableEmbedding.prodMap e.toHomeomorph.measurableEmbedding
  constructor
  · rw [thermalDensityLogIntegrand_comp_isometry]
    exact he.integrable_comp_of_integrable hG
  · unfold thermalDensityLogEnergy
    rw [thermalDensityLogIntegrand_comp_isometry]
    exact he.integral_comp hemb (thermalDensityLogIntegrand ρ)

/-- Finite-canonical-domain invariance for the ORIGINAL extended functional.
All transformed moment, entropy and interaction integrability is derived. -/
theorem thermalCanonicalFreeEnergy_map_isometry {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hfinite : equilibriumNonnegativeObjective β μ ≠ ∞)
    (e : ℂ ≃ₗᵢ[ℝ] ℂ) :
    equilibriumCanonicalFreeEnergy β (μ.map e) = equilibriumCanonicalFreeEnergy β μ := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hfinite
  have hP2 := equilibriumObjective_finite_secondMoment hfinite
  let ρ : ℂ → ℝ := equilibriumReferenceDensity μ
  let σ : ℂ → ℝ := ρ ∘ e.symm
  have hρm : Measurable ρ := equilibriumReferenceDensity_measurable μ
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumReferenceDensity_nonneg μ
  have hρi : Integrable ρ := equilibriumReferenceDensity_integrable μ
  have hρmass : (∫ x, ρ x) = 1 := integral_equilibriumReferenceDensity hAC
  have hρ2 : Integrable (fun x : ℂ => ‖x‖^2*ρ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hAC hP2
  have hρH : Integrable (fun x => ρ x*Real.log (ρ x)) :=
    equilibriumObjective_finite_entropy_integrable hβ hfinite
  have hρG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume) :=
    thermalReferenceDensity_logIntegrand_integrable hβ hfinite
  have hρlaw : equilibriumDensityMeasure ρ = (μ : Measure ℂ) :=
    equilibriumReferenceDensity_measure hAC
  have hσm : Measurable σ := hρm.comp e.symm.continuous.measurable
  have hσ0 : ∀ x, 0 ≤ σ x := fun x => hρ0 (e.symm x)
  have hσi : Integrable σ := e.symm.measurePreserving.integrable_comp_of_integrable hρi
  have hσmass : (∫ x, σ x) = 1 := by
    rw [show (∫ x, σ x) = ∫ x, ρ x from
      e.symm.measurePreserving.integral_comp e.symm.toHomeomorph.measurableEmbedding ρ]
    exact hρmass
  have hσ2 : Integrable (fun x : ℂ => ‖x‖^2*σ x) := by
    have h := e.symm.measurePreserving.integrable_comp_of_integrable hρ2
    simpa only [σ, Function.comp_def, e.symm.norm_map] using h
  have hσH : Integrable (fun x => σ x*Real.log (σ x)) := by
    simpa only [σ, Function.comp_def] using
      e.symm.measurePreserving.integrable_comp_of_integrable hρH
  obtain ⟨hσG, henergy⟩ := thermalDensityLogEnergy_isometry e.symm hρG
  have hmoment : (∫ x : ℂ, ‖x‖^2*σ x) = ∫ x : ℂ, ‖x‖^2*ρ x := by
    have h := e.symm.measurePreserving.integral_comp e.symm.toHomeomorph.measurableEmbedding
      (fun x : ℂ => ‖x‖^2*ρ x)
    simpa only [σ, Function.comp_def, e.symm.norm_map] using h
  have hentropy : (∫ x : ℂ, σ x*Real.log (σ x)) = ∫ x : ℂ, ρ x*Real.log (ρ x) := by
    exact e.symm.measurePreserving.integral_comp e.symm.toHomeomorph.measurableEmbedding
      (fun x : ℂ => ρ x*Real.log (ρ x))
  have hmaplaw : (μ.map e : Measure ℂ) = equilibriumDensityMeasure σ := by
    change Measure.map e (μ : Measure ℂ) = equilibriumDensityMeasure σ
    rw [← hρlaw, thermalDensityMeasure_map_isometry e hρm]
  have hFρ := thermalCanonicalFreeEnergy_eq_densityParts hβ hρm hρ0 hρi hρmass hρ2 hρH hρG
  have hFσ := thermalCanonicalFreeEnergy_eq_densityParts hβ hσm hσ0 hσi hσmass hσ2 hσH hσG
  calc
    equilibriumCanonicalFreeEnergy β (μ.map e) =
        equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure σ) :=
      congrArg (equilibriumCanonicalFreeEnergy β) hmaplaw
    _ = (((∫ x : ℂ, ‖x‖^2*σ x)/2 + thermalDensityLogEnergy σ/2 +
        (∫ x : ℂ, σ x*Real.log (σ x))/β : ℝ) : EReal) := hFσ
    _ = (((∫ x : ℂ, ‖x‖^2*ρ x)/2 + thermalDensityLogEnergy ρ/2 +
        (∫ x : ℂ, ρ x*Real.log (ρ x))/β : ℝ) : EReal) := by
      rw [hmoment, henergy, hentropy]
    _ = equilibriumCanonicalFreeEnergy β μ :=
      hFρ.symm.trans (congrArg (equilibriumCanonicalFreeEnergy β) hρlaw)

/-- Every original canonical minimizer is invariant under every actual real
linear isometry. Finiteness is derived from NEW attained-domain control. -/
theorem thermalCanonical_minimizer_map_isometry {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν)
    (e : ℂ ≃ₗᵢ[ℝ] ℂ) : μ.map e = μ := by
  have hfinite := (thermalCanonical_global_minimizer_finite_domain hβ hmin).2.2
  have hE := thermalCanonicalFreeEnergy_map_isometry hβ μ hfinite e
  have hminmap : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (μ.map e) ≤ equilibriumCanonicalFreeEnergy β ν := by
    intro ν
    rw [hE]
    exact hmin ν
  exact thermalCanonical_global_minimizers_unique hβ (μ.map e) μ hminmap hmin

theorem thermalCanonical_minimizer_measure_map_isometry {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν)
    (e : ℂ ≃ₗᵢ[ℝ] ℂ) : Measure.map e (μ : Measure ℂ) = (μ : Measure ℂ) := by
  exact congrArg ProbabilityMeasure.toMeasure
    (thermalCanonical_minimizer_map_isometry hβ μ hmin e)

/- Pointwise density caveat:
The theorems above are unconditional measure invariance statements. They do
not assert pointwise invariance of the canonical RN function. A continuous
density representative can be upgraded from a.e. invariance to pointwise
invariance using positivity of volume on open sets. Alternatively, the owner
is separately constructing an invariant extended logarithmic potential. A
future separately justified exponential EL representative can inherit radiality.
The reflection sending equal-norm x to y is a real linear isometry; see
Submodule.reflection_sub in Projection/Reflection.lean:152. -/

end RepulsiveCoulomb.PaperRoute
