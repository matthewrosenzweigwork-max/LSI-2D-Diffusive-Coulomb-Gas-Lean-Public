import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalStrictConvexity
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalOriginalAttainment

/-! Uniqueness of every original canonical
minimizer from new attainment-domain control, new Green-based interaction
convexity, and actual integrated strict entropy. No old uniqueness producer. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- No finite-energy, density, smoothness, EL or radiality hypothesis is added
to the all-canonical-minimizers uniqueness statement. -/
theorem thermalCanonical_global_minimizers_unique {β : ℝ} (hβ : 0 < β)
    (μ ν : ProbabilityMeasure ℂ)
    (hμ : ∀ ξ : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ξ)
    (hν : ∀ ξ : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β ν ≤ equilibriumCanonicalFreeEnergy β ξ) : μ = ν := by
  by_contra hne
  have hμF := (thermalCanonical_global_minimizer_finite_domain hβ hμ).2.2
  have hνF := (thermalCanonical_global_minimizer_finite_domain hβ hν).2.2
  obtain ⟨ξ, _, _, hs⟩ := thermalCanonicalFreeEnergy_strictConvex_finite_domain
    hβ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) μ ν hne hμF hνF
  have heq : equilibriumCanonicalFreeEnergy β μ = equilibriumCanonicalFreeEnergy β ν :=
    le_antisymm (hμ ν) (hν μ)
  obtain ⟨γ, c, hc⟩ := thermalCanonicalFreeEnergy_gaussian_finite hβ
  have hcap : equilibriumCanonicalFreeEnergy β ν ≤ (c : EReal) := by simpa only [hc] using hν γ
  have hnTop := ne_top_of_le_ne_top (EReal.coe_ne_top c) hcap
  have hnBot := thermalCanonicalFreeEnergy_ne_bot hβ ν
  have hreal := EReal.coe_toReal hnTop hnBot
  have hmean : ((1 / 2 : ℝ) : EReal) * equilibriumCanonicalFreeEnergy β μ +
      ((1 - (1 / 2 : ℝ) : ℝ) : EReal) * equilibriumCanonicalFreeEnergy β ν =
        equilibriumCanonicalFreeEnergy β μ := by
    rw [heq, ← hreal, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring
  rw [hmean] at hs
  exact (not_lt_of_ge (hμ ξ)) hs

/-- Existence and uniqueness use only the new canonical direct method and the
new strict-convexity proof. -/
theorem thermalCanonical_existsUnique_global_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃! μ : ProbabilityMeasure ℂ,
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, _, _, _, hμ⟩ := thermalCanonical_exists_global_minimizer hβ
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact thermalCanonical_global_minimizers_unique hβ ν μ hν hμ

/-- The unique original-input minimizer has the genuine finite domain as a
conclusion, inherited from the new attainment proof. -/
theorem thermalCanonical_existsUnique_finite_global_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃! μ : ProbabilityMeasure ℂ,
      (μ : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, hAC, hP2, hF, hμ⟩ := thermalCanonical_exists_global_minimizer hβ
  refine ⟨μ, ⟨hAC, hP2, hF, hμ⟩, ?_⟩
  intro ν hν
  exact thermalCanonical_global_minimizers_unique hβ ν μ hν.2.2.2 hμ

end RepulsiveCoulomb.PaperRoute
