import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCappedDensity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveFiniteEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-! Self-energy convergence for literal normalized
caps. Every dominating energy is a SELF energy; no limiting cross-energy
integrability is assumed or deduced by a totalized real integral. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

def thermalDensityLogIntegrand (ρ : ℂ → ℝ) (p : ℂ × ℂ) : ℝ :=
  equilibriumLogKernel (p.1 - p.2) * ρ p.1 * ρ p.2

def thermalDensityLogEnergy (ρ : ℂ → ℝ) : ℝ :=
  ∫ p, thermalDensityLogIntegrand ρ p ∂(volume.prod volume)

theorem thermalDensityLogIntegrand_measurable {ρ : ℂ → ℝ} (hρm : Measurable ρ) :
    Measurable (thermalDensityLogIntegrand ρ) :=
  ((equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
    (hρm.comp measurable_fst)).mul (hρm.comp measurable_snd)

/-- Exact absolute-integrability transfer in both directions under the actual
withDensity product law. -/
theorem thermalDensityLogIntegrand_integrable_iff {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume) ↔
      Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
        ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) := by
  unfold equilibriumDensityMeasure
  rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal]
  rw [integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
  apply integrable_congr
  exact Eventually.of_forall fun p => by
    dsimp only [thermalDensityLogIntegrand]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ0 p.1), ENNReal.toReal_ofReal (hρ0 p.2)]
    ring

theorem integral_thermalDensityLogIntegrand {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (_hG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ))) =
      thermalDensityLogEnergy ρ := by
  unfold equilibriumDensityMeasure thermalDensityLogEnergy
  rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    dsimp only [thermalDensityLogIntegrand]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ0 p.1),
      ENNReal.toReal_ofReal (hρ0 p.2), smul_eq_mul]
    ring

theorem thermalNormalizedDensityCap_logIntegrand_bound {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j)
    (n : ℕ) (p : ℂ × ℂ) :
    ‖thermalDensityLogIntegrand (thermalNormalizedDensityCap ρ N n) p‖ ≤
      4 * |thermalDensityLogIntegrand ρ p| := by
  have hx := thermalNormalizedDensityCap_le_two_density hρ0 hN n p.1
  have hy := thermalNormalizedDensityCap_le_two_density hρ0 hN n p.2
  have hx0 := thermalNormalizedDensityCap_nonneg hρ0 hN n p.1
  have hy0 := thermalNormalizedDensityCap_nonneg hρ0 hN n p.2
  rw [thermalDensityLogIntegrand, thermalDensityLogIntegrand,
    Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hx0, abs_of_nonneg hy0,
    abs_of_nonneg (hρ0 p.1), abs_of_nonneg (hρ0 p.2)]
  have hh := mul_le_mul hx hy hy0 (mul_nonneg (by norm_num) (hρ0 p.1))
  have hg := mul_le_mul_of_nonneg_left hh (abs_nonneg (equilibriumLogKernel (p.1 - p.2)))
  nlinarith

theorem thermalNormalizedDensityCap_logIntegrand_integrable {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    Integrable (thermalDensityLogIntegrand (thermalNormalizedDensityCap ρ N n))
      (volume.prod volume) := by
  apply (hG.abs.const_mul 4).mono'
    (thermalDensityLogIntegrand_measurable
      (thermalNormalizedDensityCap_measurable hρm N n)).aestronglyMeasurable
  exact Eventually.of_forall (thermalNormalizedDensityCap_logIntegrand_bound hρ0 hN n)

/-- Self-energy converges by an integrable four-times-self-energy majorant. -/
theorem thermalNormalizedDensityCap_logEnergy_tendsto {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x, ρ x) = 1)
    (hG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) :
    Tendsto (fun n => thermalDensityLogEnergy (thermalNormalizedDensityCap ρ N n))
      atTop (𝓝 (thermalDensityLogEnergy ρ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun p => 4 * |thermalDensityLogIntegrand ρ p|)
    (fun n => (thermalDensityLogIntegrand_measurable
      (thermalNormalizedDensityCap_measurable hρm N n)).aestronglyMeasurable)
    (hG.abs.const_mul 4)
    (fun n => Eventually.of_forall (thermalNormalizedDensityCap_logIntegrand_bound hρ0 hN n))
  exact Eventually.of_forall fun p =>
    ((thermalNormalizedDensityCap_tendsto hρm hρ0 hρi hρmass N p.1).const_mul
      (equilibriumLogKernel (p.1 - p.2))).mul
        (thermalNormalizedDensityCap_tendsto hρm hρ0 hρi hρmass N p.2)

theorem thermalCappedProbability_logEnergy_integrable {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) (N : ℕ)
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      (((thermalCappedProbability hρm hρ0 hρi N hN n : ProbabilityMeasure ℂ) : Measure ℂ).prod
        (thermalCappedProbability hρm hρ0 hρi N hN n)) :=
  (thermalDensityLogIntegrand_integrable_iff
    (thermalNormalizedDensityCap_measurable hρm N n)
    (thermalNormalizedDensityCap_nonneg hρ0 hN n)).mp
      (thermalNormalizedDensityCap_logIntegrand_integrable hρm hρ0 hG hN n)

/-- Literal measure-law self-energy convergence, after proving actual product
integrability of every term and of the limit. -/
theorem thermalCappedProbability_logEnergy_tendsto {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x, ρ x) = 1)
    (hG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume)) (N : ℕ)
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) :
    Tendsto (fun n => ∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((thermalCappedProbability hρm hρ0 hρi N hN n : Measure ℂ).prod
        (thermalCappedProbability hρm hρ0 hρi N hN n))) atTop
      (𝓝 (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
        ∂((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)))) := by
  have hn (n : ℕ) : (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((thermalCappedProbability hρm hρ0 hρi N hN n : Measure ℂ).prod
        (thermalCappedProbability hρm hρ0 hρi N hN n))) =
      thermalDensityLogEnergy (thermalNormalizedDensityCap ρ N n) :=
    integral_thermalDensityLogIntegrand
      (thermalNormalizedDensityCap_measurable hρm N n)
      (thermalNormalizedDensityCap_nonneg hρ0 hN n)
      (thermalNormalizedDensityCap_logIntegrand_integrable hρm hρ0 hG hN n)
  simpa only [hn, integral_thermalDensityLogIntegrand hρm hρ0 hG] using
    thermalNormalizedDensityCap_logEnergy_tendsto hρm hρ0 hρi hρmass hG hN

/-- Extract the actual RN density's genuine self-energy from finite canonical
objective data. No cross-density energy occurs in this statement. -/
theorem thermalReferenceDensity_logIntegrand_integrable {β : ℝ} (hβ : 0 < β)
    {μ : ProbabilityMeasure ℂ} (hF : equilibriumNonnegativeObjective β μ ≠ ∞) :
    Integrable (thermalDensityLogIntegrand (equilibriumReferenceDensity μ))
      (volume.prod volume) := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hF
  apply (thermalDensityLogIntegrand_integrable_iff
    (equilibriumReferenceDensity_measurable μ)
    (equilibriumReferenceDensity_nonneg μ)).mpr
  rw [equilibriumReferenceDensity_measure hAC]
  exact equilibriumObjective_finite_logEnergy_integrable hβ hF

/-- The normalization tail is produced, not postulated, for every canonical
finite-objective probability. The approximants are the literal normalized caps
of its actual RN density, with genuine self energies, weak convergence and P². -/
theorem thermalFiniteObjective_exists_capped_approximants {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hF : equilibriumNonnegativeObjective β μ ≠ ∞) :
    ∃ (N : ℕ) (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤
      thermalDensityCapMass (equilibriumReferenceDensity μ) j),
      1 ≤ N ∧
      Tendsto (thermalCappedProbability (equilibriumReferenceDensity_measurable μ)
        (equilibriumReferenceDensity_nonneg μ) (equilibriumReferenceDensity_integrable μ) N hN)
        atTop (𝓝 μ) ∧
      (∀ n, Integrable (fun x : ℂ => ‖x‖ ^ 2)
        (thermalCappedProbability (equilibriumReferenceDensity_measurable μ)
          (equilibriumReferenceDensity_nonneg μ) (equilibriumReferenceDensity_integrable μ) N hN n)) ∧
      (∀ n, (∫ x : ℂ, ‖x‖ ^ 2 ∂(thermalCappedProbability
        (equilibriumReferenceDensity_measurable μ) (equilibriumReferenceDensity_nonneg μ)
        (equilibriumReferenceDensity_integrable μ) N hN n)) ≤ 2 * (∫ x : ℂ, ‖x‖ ^ 2 ∂μ)) ∧
      Tendsto (fun n => ∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
        ∂((thermalCappedProbability (equilibriumReferenceDensity_measurable μ)
          (equilibriumReferenceDensity_nonneg μ) (equilibriumReferenceDensity_integrable μ) N hN n : Measure ℂ).prod
          (thermalCappedProbability (equilibriumReferenceDensity_measurable μ)
            (equilibriumReferenceDensity_nonneg μ) (equilibriumReferenceDensity_integrable μ) N hN n)))
        atTop (𝓝 (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂((μ : Measure ℂ).prod μ))) := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hF
  have hP2 := equilibriumObjective_finite_secondMoment hF
  have hm := equilibriumReferenceDensity_measurable (μ : Measure ℂ)
  have h0 := equilibriumReferenceDensity_nonneg (μ : Measure ℂ)
  have hi := equilibriumReferenceDensity_integrable (μ : Measure ℂ)
  have hmass := integral_equilibriumReferenceDensity hAC
  have h2 := equilibriumReferenceDensity_secondMoment_integrable hAC hP2
  have hG := thermalReferenceDensity_logIntegrand_integrable hβ hF
  obtain ⟨N, hN1, hN⟩ := thermalDensityCapMass_exists_half_tail hm h0 hi hmass
  refine ⟨N, hN, hN1, ?_, ?_, ?_, ?_⟩
  · have hw := thermalCappedProbability_weak_tendsto hm h0 hi hmass N hN
    have he : (⟨equilibriumDensityMeasure (equilibriumReferenceDensity μ),
        equilibriumDensityMeasure_probability h0 hi hmass⟩ : ProbabilityMeasure ℂ) = μ := by
      apply Subtype.ext
      exact equilibriumReferenceDensity_measure hAC
    simpa only [he] using hw
  · intro n
    exact (thermalCappedProbability_secondMoment hm h0 hi h2 N hN n).1
  · intro n
    simpa only [integral_equilibriumReferenceDensity_secondMoment hAC] using
      (thermalCappedProbability_secondMoment hm h0 hi h2 N hN n).2
  · simpa only [equilibriumReferenceDensity_measure hAC] using
      thermalCappedProbability_logEnergy_tendsto hm h0 hi hmass hG N hN

end RepulsiveCoulomb.PaperRoute
