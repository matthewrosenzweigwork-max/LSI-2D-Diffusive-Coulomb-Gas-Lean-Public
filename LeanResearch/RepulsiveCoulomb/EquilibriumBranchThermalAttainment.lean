module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveCompactness
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGaussianObjective

@[expose] public section

/-! Actual direct-method attainment for every beta>0. A finite Gaussian
sublevel is proved nonempty and compact; its minimizer is proved globally
minimizing, and AC/P2 are conclusions of finite objective. Uniqueness,
Euler--Lagrange, regularity and compact-temperature estimates remain later
construction steps, not hypotheses of this attainment theorem. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

/-- The full nonnegative objective attains a global finite minimum over every
planar probability measure, including singular and non-P2 competitors. -/
theorem equilibriumObjective_exists_global_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      (μ : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumNonnegativeObjective β μ ≤ equilibriumNonnegativeObjective β ν := by
  have ha : 0 < β / 4 := by positivity
  let γ : ProbabilityMeasure ℂ := equilibriumGaussianProbability (β / 4) ha
  let C : ℝ≥0∞ := equilibriumNonnegativeObjective β γ
  let S : Set (ProbabilityMeasure ℂ) := {μ | equilibriumNonnegativeObjective β μ ≤ C}
  have hC : C ≠ ∞ := equilibriumGaussianObjective_ne_top hβ
  have hS : S.Nonempty := ⟨γ, by
    change equilibriumNonnegativeObjective β γ ≤ equilibriumNonnegativeObjective β γ
    exact le_rfl⟩
  have hcompact : IsCompact S := equilibriumObjective_sublevel_isCompact hβ hC
  obtain ⟨μ, hμS, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hS hcompact
    ((equilibriumObjective_lowerSemicontinuous hβ).lowerSemicontinuousOn S)
  have hμfinite : equilibriumNonnegativeObjective β μ ≠ ∞ :=
    ((show equilibriumNonnegativeObjective β μ ≤ C from hμS).trans_lt (lt_top_iff_ne_top.mpr hC)).ne
  refine ⟨μ, hμfinite, equilibriumObjective_finite_absolutelyContinuous hβ hμfinite,
    equilibriumObjective_finite_secondMoment hμfinite, ?_⟩
  intro ν
  by_cases hν : ν ∈ S
  · exact (isMinOn_iff.mp hmin) ν hν
  · have hν' : C < equilibriumNonnegativeObjective β ν := lt_of_not_ge hν
    exact (show equilibriumNonnegativeObjective β μ ≤ C from hμS).trans hν'.le

/-- The attained measure really minimizes the unchanged canonical free energy
with its infinite convention, by the full extended correspondence and the
explicit fixed normalization shift. -/
theorem equilibriumCanonical_exists_global_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      (μ : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, hfinite, hAC, hP2, hmin⟩ := equilibriumObjective_exists_global_minimizer hβ
  refine ⟨μ, hAC, hP2, hfinite, ?_⟩
  intro ν
  by_cases hν : (ν : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) ν
  · rw [equilibriumFreeEnergy_correspondence hβ hP2,
      equilibriumFreeEnergy_correspondence hβ hν.2,
      equilibriumNonnegativeFreeEnergy_eq_objective, equilibriumNonnegativeFreeEnergy_eq_objective]
    have hle := EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmin ν)
    exact add_le_add (EReal.sub_le_sub hle le_rfl) le_rfl
  · have htop : equilibriumCanonicalFreeEnergy β ν = ⊤ := by
      unfold equilibriumCanonicalFreeEnergy
      exact if_neg hν
    rw [htop]
    exact le_top

end RepulsiveCoulomb
