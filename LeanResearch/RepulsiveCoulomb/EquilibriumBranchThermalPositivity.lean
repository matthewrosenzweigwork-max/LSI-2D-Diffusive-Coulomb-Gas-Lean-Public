module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalAttainment
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveFiniteEnergy
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchUniformSetDensity
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchMixtureDecrease

@[expose] public section

/-! Actual positivity of an attained thermal minimizer. A genuine normalized
finite-energy filling density is constructed in any positive-volume zero set;
the exact entropy-mixture decrease contradicts global minimality. No EL,
boundedness, radiality, regularity or infinite derivative is an input. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumDensityMeasure_energy_to_density {ρ : ℂ → ℝ}
    (hm : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ))) :
    Integrable (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2))
      (volume.prod volume) := by
  unfold equilibriumDensityMeasure at hG
  rw [prod_withDensity hm.ennreal_ofReal hm.ennreal_ofReal] at hG
  have hi := (integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))).mp hG
  apply hi.congr
  exact Eventually.of_forall (fun p => by
    dsimp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 p.1), ENNReal.toReal_ofReal (h0 p.2)]
    ring)

/-- Every actual finite-objective canonical minimizer has positive density
planar-a.e. All finite-energy variation conditions are conclusions or proved
properties of the explicitly constructed filler. -/
theorem equilibriumCanonicalMinimizer_density_positive_ae {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hfinite : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∀ᵐ x : ℂ, 0 < equilibriumReferenceDensity μ x := by
  let ρ : ℂ → ℝ := equilibriumReferenceDensity μ
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hfinite
  have hP2 := equilibriumObjective_finite_secondMoment hfinite
  have hρm : Measurable ρ := equilibriumReferenceDensity_measurable μ
  have hρ0 : ∀ x, 0 ≤ ρ x := equilibriumReferenceDensity_nonneg μ
  have hρi : Integrable ρ := equilibriumReferenceDensity_integrable μ
  have hρmass : (∫ x : ℂ, ρ x) = 1 := integral_equilibriumReferenceDensity hAC
  have hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) :=
    equilibriumReferenceDensity_secondMoment_integrable hAC hP2
  have hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)) :=
    equilibriumObjective_finite_entropy_integrable hβ hfinite
  have hρmeasure : equilibriumDensityMeasure ρ = (μ : Measure ℂ) := equilibriumReferenceDensity_measure hAC
  have hρGμ : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) := by
    rw [hρmeasure]
    exact equilibriumObjective_finite_logEnergy_integrable hβ hfinite
  have hRR := equilibriumDensityMeasure_energy_to_density hρm hρ0 hρGμ
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hzero : volume {x : ℂ | ρ x = 0} = 0 := by
    by_contra hzero
    obtain ⟨A, R, hA, hA0, hAfin, hR, hAR, hAρ⟩ := equilibrium_zeroSet_contains_filling_set hρm hzero
    let ψ : ℂ → ℝ := equilibriumUniformSetDensity A
    have hψm : Measurable ψ := equilibriumUniformSetDensity_measurable hA
    have hψ0 : ∀ x, 0 ≤ ψ x := equilibriumUniformSetDensity_nonneg A
    have hψM : ∀ x, ψ x ≤ ((volume A).toReal)⁻¹ := equilibriumUniformSetDensity_le A
    have hψi : Integrable ψ := equilibriumUniformSetDensity_integrable hA hAfin
    have hψmass : (∫ x : ℂ, ψ x) = 1 := integral_equilibriumUniformSetDensity hA hA0 hAfin
    have hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x) :=
      equilibriumUniformSetDensity_secondMoment_integrable hA hAfin hR.le hAR
    have hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)) :=
      equilibriumUniformSetDensity_entropy_integrable hA hAfin
    have hψL := equilibriumLogMoment_mul_integrable hψm hψ0 hψi hψ2
    have hSS := equilibriumUniformSetDensity_logEnergy_integrable hA hA0 hAfin hR.le hAR
    have hRS := equilibriumCrossInteraction_integrable hρm hρ0 hρi hρL
      hψm hψ0 hψM hψi hψmass hψL
    have hdisj : ∀ᵐ x : ℂ, ρ x * ψ x = 0 :=
      Eventually.of_forall (equilibriumUniformSetDensity_disjoint hAρ)
    obtain ⟨ε, hε, hdec⟩ := equilibriumDensityFreeEnergy_exists_disjoint_decrease hβ
      hρ0 hψ0 hdisj hρi hψi hρmass hψmass hρ2 hψ2 hρH hψH hRR hRS hSS
    let φ : ℂ → ℝ := equilibriumDensityMixture ε ρ ψ
    have hφm : Measurable φ := equilibriumDensityMixture_measurable ε hρm hψm
    have hφ0 : ∀ x, 0 ≤ φ x := equilibriumDensityMixture_nonneg hε.1.le hε.2.le hρ0 hψ0
    have hφi : Integrable φ := equilibriumDensityMixture_integrable ε hρi hψi
    have hφmass : (∫ x : ℂ, φ x) = 1 := integral_equilibriumDensityMixture ε hρi hψi hρmass hψmass
    have hφ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * φ x) :=
      equilibriumDensityMixture_secondMoment_integrable ε hρ2 hψ2
    have hφH : Integrable (fun x : ℂ => φ x * Real.log (φ x)) :=
      equilibrium_disjoint_mixture_entropy_integrable hρ0 hψ0 hdisj hρi hψi hρH hψH hε.1 hε.2
    have hφG := equilibriumDensityMixture_logEnergy_integrable ε hRR hRS hSS
    letI := equilibriumDensityMeasure_probability hφ0 hφi hφmass
    let ν : ProbabilityMeasure ℂ := ⟨equilibriumDensityMeasure φ, inferInstance⟩
    have hFρ := equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hρm hρ0 hρi hρmass hρ2 hρH hRR
    rw [hρmeasure] at hFρ
    have hFφ := equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hφm hφ0 hφi hφmass hφ2 hφH hφG
    have hcmp := hmin ν
    change equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure φ) at hcmp
    rw [hFρ, hFφ] at hcmp
    exact (not_le_of_gt hdec) (EReal.coe_le_coe_iff.mp hcmp)
  have ha : ∀ᵐ x : ℂ, x ∉ {x : ℂ | ρ x = 0} := compl_mem_ae_iff.mpr hzero
  filter_upwards [ha] with x hx
  change ρ x ≠ 0 at hx
  exact lt_of_le_of_ne (hρ0 x) hx.symm

/-- Positive-density attainment is a conclusion for each beta>0, obtained from
the actual direct method and the proved zero-set contradiction above. -/
theorem equilibriumCanonical_exists_positive_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ProbabilityMeasure ℂ, equilibriumNonnegativeObjective β μ ≠ ∞ ∧
      (∀ᵐ x : ℂ, 0 < equilibriumReferenceDensity μ x) ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, hAC, hP2, hfinite, hmin⟩ := equilibriumCanonical_exists_global_minimizer hβ
  exact ⟨μ, hfinite, equilibriumCanonicalMinimizer_density_positive_ae hβ μ hfinite hmin, hmin⟩

end RepulsiveCoulomb
