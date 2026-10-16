module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalSharpCap
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalMoment

@[expose] public section

/-! Packaging only of properties already proved by the direct-method and
variation chain. The reference is genuinely constructed for every beta>0;
no existence, EL, regularity, cap or moment property is postulated. Quantitative
higher derivative tails and compact-temperature estimates remain additional
results, not fields silently assumed by this intermediate package. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

structure EquilibriumConstructedReference (β : ℝ) where
  measure : ProbabilityMeasure ℂ
  density : ℂ → ℝ
  elConstant : ℝ
  tailConstant : ℝ
  objective_finite : equilibriumNonnegativeObjective β measure ≠ ∞
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) density
  positive : ∀ x, 0 < density x
  cap : ∀ x, density x ≤ Real.pi⁻¹
  integrable : Integrable density
  mass_one : (∫ x : ℂ, density x) = 1
  secondMoment_integrable : Integrable (fun x : ℂ => ‖x‖ ^ 2 * density x)
  entropy_integrable : Integrable (fun x : ℂ => density x * Real.log (density x))
  density_measure : equilibriumDensityMeasure density = (measure : Measure ℂ)
  radial : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → density x = density y
  eulerLagrange : ∀ x, Real.log (density x) =
    -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential density x) + elConstant
  secondMoment : (∫ x : ℂ, ‖x‖ ^ 2 * density x) = 1 / 2 + 2 / β
  tailConstant_pos : 0 < tailConstant
  tail : ∀ x, density x ≤ tailConstant * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)
  minimizing : ∀ ν : ProbabilityMeasure ℂ,
    equilibriumCanonicalFreeEnergy β measure ≤ equilibriumCanonicalFreeEnergy β ν

/-- The intermediate reference package is nonempty by the actual construction. -/
theorem equilibriumConstructedReference_nonempty {β : ℝ} (hβ : 0 < β) :
    Nonempty (EquilibriumConstructedReference β) := by
  obtain ⟨μ, hAC, hP2, hfinite, hmin⟩ := equilibriumCanonical_exists_global_minimizer hβ
  obtain ⟨ρ, C, M, K, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρμ, hEL, hK, htail⟩ :=
    equilibriumCanonicalMinimizer_exists_bounded_EL_density hβ μ hfinite hmin
  have hρ0 := fun x => (hρpos x).le
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y := by
    intro x y hxy
    exact equilibrium_pointwise_EL_radial hβ hρm hρpos hρM hρi hρmass hρL hEL hxy
  have hsmooth := equilibrium_pointwise_EL_contDiff hβ hρm hρpos hρM hρi hρmass hρ2 hrad hEL
  have hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ →
      equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y := by
    intro x y hxy
    exact equilibriumDensityPotential_radial_of_EL hβ hrad hEL hxy
  have hUc := (equilibriumDensityPotential_contDiff_one hρm hρ0 hρM hρi hρmass hρ2 hUrad).continuous
  have hcap := equilibrium_pointwise_EL_sharp_cap hβ hsmooth.continuous hρpos hρM hρi hρmass hρ2 hUc hEL
  have hmμ := equilibriumCanonicalMinimizer_secondMoment hβ μ hfinite hmin
  have he : (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) = ∫ x : ℂ, ‖x‖ ^ 2 ∂μ := by
    rw [← hρμ, integral_equilibriumDensityMeasure hρm hρ0]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  have hm : (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) = 1 / 2 + 2 / β := he.trans hmμ
  exact ⟨⟨μ, ρ, C, K, hfinite, hsmooth, hρpos, hcap, hρi, hρmass, hρ2, hρH,
    hρμ, hrad, hEL, hm, hK, htail, hmin⟩⟩

/-- The actual selected reference, with existence proved immediately above. -/
def equilibriumConstructedReference (β : ℝ) (hβ : 0 < β) : EquilibriumConstructedReference β :=
  Classical.choice (equilibriumConstructedReference_nonempty hβ)

/-- Its measure is unique among all actual finite-objective canonical minima. -/
theorem equilibriumConstructedReference_measure_unique {β : ℝ} (hβ : 0 < β)
    (ν : ProbabilityMeasure ℂ) (hνfinite : equilibriumNonnegativeObjective β ν ≠ ∞)
    (hνmin : ∀ ξ : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β ν ≤ equilibriumCanonicalFreeEnergy β ξ) :
    (equilibriumConstructedReference β hβ).measure = ν :=
  equilibriumCanonicalMinimizers_unique hβ _ ν
    (equilibriumConstructedReference β hβ).objective_finite hνfinite
    (equilibriumConstructedReference β hβ).minimizing hνmin

end RepulsiveCoulomb
