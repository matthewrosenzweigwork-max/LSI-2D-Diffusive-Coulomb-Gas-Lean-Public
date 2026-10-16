module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalSharpCap
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference

@[expose] public section

/-! The unchanged physical reference record is populated from the SAME
actual positive smooth sharply capped EL density of a NEW canonical
minimizer. The missing exact second-moment field is derived by the generic
conditional normalized-dilation variation on that density. No old reference
constructor or selector is used. Higher-derivative tails are a separate
clause and are not fields of this record. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- Build a physical reference whose measure is literally the supplied NEW
canonical minimizer. Every density field belongs to its one chosen EL
representative; the normalized-dilation identity proves the exact moment. -/
theorem thermal_physicalReference_from_minimizer {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ R : EquilibriumConstructedReference β, R.measure = μ := by
  have hfinite := (thermalCanonical_global_minimizer_finite_domain hβ hmin).2.2
  obtain ⟨ρ, C, M, K, hcap, hρsmooth, hUsmooth, hm, hpos, hM, hbound, hi, hmass,
    h2, hH, hlaw, hEL, hK, htail, hGpoint, hUrad, hrad, hρC1, hUC1,
    hweakU, hweakDU, hLp, hHolder, hPoisson⟩ :=
    thermalCanonical_minimizer_exists_capped_smooth_EL_density hβ μ hmin
  have h0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  have hGμ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1-p.2))
      ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) := by
    rw [hlaw]
    exact equilibriumObjective_finite_logEnergy_integrable hβ hfinite
  have hG := equilibriumDensityMeasure_energy_to_density hm h0 hGμ
  have hminρ : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤
        equilibriumCanonicalFreeEnergy β ν := by
    intro ν
    rw [hlaw]
    exact hmin ν
  have hmoment := equilibriumDensityMinimizer_secondMoment
    hβ hm h0 hi hmass h2 hH hG hminρ
  exact ⟨{
    measure := μ
    density := ρ
    elConstant := C
    tailConstant := K
    objective_finite := hfinite
    smooth := hρsmooth
    positive := hpos
    cap := hcap
    integrable := hi
    mass_one := hmass
    secondMoment_integrable := h2
    entropy_integrable := hH
    density_measure := hlaw
    radial := hrad
    eulerLagrange := hEL
    secondMoment := hmoment
    tailConstant_pos := hK
    tail := htail
    minimizing := hmin }, rfl⟩

/-- Original-input existence, through NEW canonical attainment and the new
EL/radiality/Poisson/regularity/smoothness/maximum-Laplacian cap chain. -/
theorem thermalConstructedReference_nonempty {β : ℝ} (hβ : 0 < β) :
    Nonempty (EquilibriumConstructedReference β) := by
  obtain ⟨μ, _, _, _, hmin⟩ := thermalCanonical_exists_global_minimizer hβ
  obtain ⟨R, _⟩ := thermal_physicalReference_from_minimizer hβ μ hmin
  exact ⟨R⟩

/-- The new physical reference selector. Its existence proof is the new
route above, not the old frozen reference selector. -/
def thermalConstructedReference (β : ℝ) (hβ : 0 < β) : EquilibriumConstructedReference β :=
  Classical.choice (thermalConstructedReference_nonempty hβ)

/-- The selected measure is the unique global canonical minimizer, with
no finite-energy premise placed on its competitor. -/
theorem thermalConstructedReference_measure_unique {β : ℝ} (hβ : 0 < β)
    (ν : ProbabilityMeasure ℂ)
    (hmin : ∀ ξ : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β ν ≤ equilibriumCanonicalFreeEnergy β ξ) :
    (thermalConstructedReference β hβ).measure = ν :=
  thermalCanonical_global_minimizers_unique hβ _ ν
    (thermalConstructedReference β hβ).minimizing hmin

end RepulsiveCoulomb.PaperRoute
