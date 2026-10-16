import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalSequence
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalWeakLSC

/-! Original-input canonical thermal existence through a literal minimizing
sequence, exact quarter coercivity, Markov/Prokhorov extraction, and the new
positive/negative logarithmic semicontinuity route. No old objective minimizer
or objective-LSC producer is used. This proves existence, not uniqueness,
Green convexity, Euler-Lagrange regularity, or normalized thermal identification. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Every global canonical minimizer has finite original objective, absolute
continuity and a genuine second moment. This uses only a Gaussian comparison,
not any old or new existence theorem. -/
theorem thermalCanonical_global_minimizer_finite_domain {β : ℝ} (hβ : 0 < β)
    {μ : ProbabilityMeasure ℂ}
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    (μ : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      equilibriumNonnegativeObjective β μ ≠ ∞ := by
  obtain ⟨γ, c, hc⟩ := thermalCanonicalFreeEnergy_gaussian_finite hβ
  have hcap : equilibriumCanonicalFreeEnergy β μ ≤ (c : EReal) := by
    simpa only [hc] using hmin γ
  have hn := ne_top_of_le_ne_top (EReal.coe_ne_top c) hcap
  obtain ⟨hAC, hP2⟩ := thermalCanonicalFreeEnergy_ne_top_domain hn
  refine ⟨hAC, hP2, ?_⟩
  intro htop
  apply hn
  rw [equilibriumFreeEnergy_correspondence hβ hP2,
    equilibriumNonnegativeFreeEnergy_eq_objective, htop,
    EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.top_add_coe]

/-- An actual finite-objective canonical minimizer. All domain and compactness
conditions are conclusions of the literal canonical direct method. -/
theorem thermalCanonical_exists_global_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ,
      (μ : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨e, c, M, μs, _, hP2, hM, henergy, hlower⟩ :=
    thermalCanonicalFreeEnergy_exists_minimizingSequence hβ
  obtain ⟨μ, φ, hφ, hweak⟩ :=
    thermal_uniformSecondMoment_exists_weak_subsequence hP2 hM
  have hlim := thermalCanonicalFreeEnergy_le_liminf_of_uniform_secondMoment hβ hweak
    (fun n => hP2 (φ n)) (fun n => hM (φ n))
  have he : Tendsto (fun n => equilibriumCanonicalFreeEnergy β ((μs ∘ φ) n))
      atTop (𝓝 (e : EReal)) := by
    simpa only [Function.comp_def] using henergy.comp hφ.tendsto_atTop
  rw [he.liminf_eq] at hlim
  have hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν :=
    fun ν => hlim.trans (hlower ν)
  obtain ⟨hAC, hP2μ, hobj⟩ := thermalCanonical_global_minimizer_finite_domain hβ hmin
  exact ⟨μ, hAC, hP2μ, hobj, hmin⟩

end RepulsiveCoulomb.PaperRoute
