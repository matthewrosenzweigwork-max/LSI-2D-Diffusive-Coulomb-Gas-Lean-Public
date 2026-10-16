import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalStrictEntropy
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalFiniteEnergyConvexity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFiniteDensityEnergy

/-! Strict convexity of the unchanged canonical
free energy, after all self/mixed entropy and interaction integrability has
been proved. No equilibrium EL, old positivity, or old uniqueness is used. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Exact finite-density algebra, with all three genuine integrability
conditions explicit and with the literal product interaction. -/
theorem thermalCanonicalFreeEnergy_eq_densityParts {β : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x => ρ x * Real.log (ρ x)))
    (hρG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) :
    equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) =
      (((∫ x : ℂ, ‖x‖ ^ 2 * ρ x) / 2 + thermalDensityLogEnergy ρ / 2 +
        (∫ x, ρ x * Real.log (ρ x)) / β : ℝ) : EReal) := by
  have hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume) := by
    apply hρG.congr
    exact Eventually.of_forall fun p => by dsimp [thermalDensityLogIntegrand]; ring
  have hI : equilibriumDensityInteraction ρ = thermalDensityLogEnergy ρ := by
    rw [equilibriumDensityInteraction_eq_product hG]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp [thermalDensityLogIntegrand]; ring
  rw [equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hρm hρ0 hρi hρmass hρ2 hρH hG]
  simp only [equilibriumDensityFreeEnergy, hI]

/-- Actual strict canonical convexity on unequal finite-objective laws. The
mixture is the literal affine probability law. Its finite objective is a
conclusion, and no interaction or entropy condition is imposed on it. -/
theorem thermalCanonicalFreeEnergy_strictConvex_finite_domain
    {β t : ℝ} (hβ : 0 < β) (ht0 : 0 < t) (ht1 : t < 1)
    (μ ν : ProbabilityMeasure ℂ) (hne : μ ≠ ν)
    (hμF : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hνF : equilibriumNonnegativeObjective β ν ≠ ∞) :
    ∃ ξ : ProbabilityMeasure ℂ,
      (ξ : Measure ℂ) = ENNReal.ofReal t • (μ : Measure ℂ) +
        ENNReal.ofReal (1 - t) • (ν : Measure ℂ) ∧
      equilibriumNonnegativeObjective β ξ ≠ ∞ ∧
      equilibriumCanonicalFreeEnergy β ξ <
        (t : EReal) * equilibriumCanonicalFreeEnergy β μ +
          ((1 - t : ℝ) : EReal) * equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨ξ, hξdensity, hξaffine, hξAC, hξP2, hξG, hE⟩ :=
    thermalInteraction_convex_on_finite_canonical_domain hβ ht0.le ht1.le μ ν hμF hνF
  have hμAC := equilibriumObjective_finite_absolutelyContinuous hβ hμF
  have hνAC := equilibriumObjective_finite_absolutelyContinuous hβ hνF
  have hμP2 := equilibriumObjective_finite_secondMoment hμF
  have hνP2 := equilibriumObjective_finite_secondMoment hνF
  let ρ := equilibriumReferenceDensity (μ : Measure ℂ)
  let σ := equilibriumReferenceDensity (ν : Measure ℂ)
  let m := thermalDensityMixture t ρ σ
  have hρm : Measurable ρ := equilibriumReferenceDensity_measurable μ
  have hσm : Measurable σ := equilibriumReferenceDensity_measurable ν
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumReferenceDensity_nonneg μ
  have hσ0 : ∀ x, 0 ≤ σ x := equilibriumReferenceDensity_nonneg ν
  have hρi : Integrable ρ := equilibriumReferenceDensity_integrable μ
  have hσi : Integrable σ := equilibriumReferenceDensity_integrable ν
  have hρmass : (∫ x, ρ x) = 1 := integral_equilibriumReferenceDensity hμAC
  have hσmass : (∫ x, σ x) = 1 := integral_equilibriumReferenceDensity hνAC
  have hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hμAC hμP2
  have hσ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * σ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hνAC hνP2
  have hρH : Integrable (fun x => ρ x * Real.log (ρ x)) := equilibriumObjective_finite_entropy_integrable hβ hμF
  have hσH : Integrable (fun x => σ x * Real.log (σ x)) := equilibriumObjective_finite_entropy_integrable hβ hνF
  have hρG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume) :=
    thermalReferenceDensity_logIntegrand_integrable hβ hμF
  have hσG : Integrable (thermalDensityLogIntegrand σ) (volume.prod volume) :=
    thermalReferenceDensity_logIntegrand_integrable hβ hνF
  have hρlaw : equilibriumDensityMeasure ρ = (μ : Measure ℂ) := equilibriumReferenceDensity_measure hμAC
  have hσlaw : equilibriumDensityMeasure σ = (ν : Measure ℂ) := equilibriumReferenceDensity_measure hνAC
  have hneρσ : ¬ ρ =ᵐ[volume] σ := by
    intro h
    apply hne
    apply ProbabilityMeasure.toMeasure_injective
    have he : equilibriumDensityMeasure ρ = equilibriumDensityMeasure σ :=
      withDensity_congr_ae (h.mono fun x hx => congrArg ENNReal.ofReal hx)
    exact hρlaw.symm.trans (he.trans hσlaw)
  have hmm : Measurable m := thermalDensityMixture_measurable hρm hσm t
  have hm0 : ∀ x, 0 ≤ m x := thermalDensityMixture_nonneg hρ0 hσ0 ht0.le ht1.le
  have hmi : Integrable m := thermalDensityMixture_integrable hρi hσi t
  have hmass : (∫ x, m x) = 1 := thermalDensityMixture_integral hρi hσi hρmass hσmass t
  have hm2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * m x) :=
    thermalDensityMixture_secondMoment_integrable hρ2 hσ2 t
  have hmH : Integrable (fun x => m x * Real.log (m x)) :=
    thermalDensityMixture_entropy_integrable ht0.le ht1.le hρm hσm hρ0 hσ0 hρi hσi hρ2 hσ2 hρH hσH
  have hmG : Integrable (thermalDensityLogIntegrand m) (volume.prod volume) := by
    apply (thermalDensityLogIntegrand_integrable_iff hmm hm0).mpr
    simpa only [hξdensity] using hξG
  have hEm : (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((ξ : Measure ℂ).prod ξ)) =
      thermalDensityLogEnergy m := by
    rw [hξdensity]
    exact integral_thermalDensityLogIntegrand hmm hm0 hmG
  have hEr : (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((μ : Measure ℂ).prod μ)) =
      thermalDensityLogEnergy ρ := by
    rw [← hρlaw]
    exact integral_thermalDensityLogIntegrand hρm hρ0 hρG
  have hEs : (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((ν : Measure ℂ).prod ν)) =
      thermalDensityLogEnergy σ := by
    rw [← hσlaw]
    exact integral_thermalDensityLogIntegrand hσm hσ0 hσG
  rw [hEm, hEr, hEs] at hE
  have hH := thermalDensityMixture_entropy_strict ht0 ht1 hρ0 hσ0 hρH hσH hmH hneρσ
  have hFξ : equilibriumCanonicalFreeEnergy β ξ =
      (((∫ x : ℂ, ‖x‖ ^ 2 * m x) / 2 + thermalDensityLogEnergy m / 2 +
        (∫ x, m x * Real.log (m x)) / β : ℝ) : EReal) := by
    rw [hξdensity]
    exact thermalCanonicalFreeEnergy_eq_densityParts hβ hmm hm0 hmi hmass hm2 hmH hmG
  have hFr : equilibriumCanonicalFreeEnergy β μ =
      (((∫ x : ℂ, ‖x‖ ^ 2 * ρ x) / 2 + thermalDensityLogEnergy ρ / 2 +
        (∫ x, ρ x * Real.log (ρ x)) / β : ℝ) : EReal) := by
    rw [← hρlaw]
    exact thermalCanonicalFreeEnergy_eq_densityParts hβ hρm hρ0 hρi hρmass hρ2 hρH hρG
  have hFs : equilibriumCanonicalFreeEnergy β ν =
      (((∫ x : ℂ, ‖x‖ ^ 2 * σ x) / 2 + thermalDensityLogEnergy σ / 2 +
        (∫ x, σ x * Real.log (σ x)) / β : ℝ) : EReal) := by
    rw [← hσlaw]
    exact thermalCanonicalFreeEnergy_eq_densityParts hβ hσm hσ0 hσi hσmass hσ2 hσH hσG
  have hξnotTop : equilibriumCanonicalFreeEnergy β ξ ≠ ⊤ := by rw [hFξ]; exact EReal.coe_ne_top _
  have hξF : equilibriumNonnegativeObjective β ξ ≠ ∞ := by
    intro ht
    apply hξnotTop
    rw [equilibriumFreeEnergy_correspondence hβ hξP2,
      equilibriumNonnegativeFreeEnergy_eq_objective, ht,
      EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.top_add_coe]
  refine ⟨ξ, hξaffine, hξF, ?_⟩
  rw [hFξ, hFr, hFs, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  have hMom := thermalDensityMixture_secondMoment_integral hρ2 hσ2 t
  have hHdiv := div_lt_div_of_pos_right hH hβ
  have hdiv : (t * (∫ x, ρ x * Real.log (ρ x)) + (1 - t) * (∫ x, σ x * Real.log (σ x))) / β =
      t * ((∫ x, ρ x * Real.log (ρ x)) / β) + (1 - t) * ((∫ x, σ x * Real.log (σ x)) / β) := by ring
  rw [hdiv] at hHdiv
  change (∫ x : ℂ, ‖x‖ ^ 2 * m x) = _ at hMom
  change (∫ x, m x * Real.log (m x)) / β < _ at hHdiv
  rw [hMom]
  nlinarith

end RepulsiveCoulomb.PaperRoute
