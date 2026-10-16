module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleEmpirical
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCommonMeasureEnergy
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveFiniteEnergy

@[expose] public section

/-! Actual signed-measure repulsivity for the singular circle-smeared empirical
probability and a finite-objective reference. The common measure, nonatomicity,
zero mass, support separation and all three absolute logarithmic energies are
discharged here. No planar-density positivity theorem is applied to circles. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumMeasure_norm_integrable_of_secondMoment {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) : Integrable (fun x : ℂ => ‖x‖) μ := by
  apply (hμ2.add (integrable_const 1)).mono' continuous_norm.measurable.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    nlinarith [sq_nonneg (‖x‖ - 1)])

/-- The actual circular empirical measure satisfies the signed Coulomb energy
inequality against every finite-objective reference. This includes all thermal
references once their already constructed finite objective is supplied. -/
theorem equilibriumCircleEmpirical_reference_repulsive {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    0 ≤ (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumCircleEmpirical z ε).prod (equilibriumCircleEmpirical z ε)) -
      2 * (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
        ∂(equilibriumCircleEmpirical z ε).prod μ) +
      (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2) ∂μ.prod μ) := by
  letI := equilibriumCircleEmpirical_probability hN z ε
  letI := equilibriumCircleEmpirical_nullSingleton z hε
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hG
  letI : NullSingletonClass μ := ⟨fun x => hAC (measure_singleton x)⟩
  have hμnorm := equilibriumMeasure_norm_integrable_of_secondMoment
    (equilibriumObjective_finite_secondMoment hG)
  exact equilibriumMutuallySingular_logRepulsive
    (equilibriumCircleEmpiricalSupport_measurable z ε)
    (equilibriumCircleEmpirical_supported z hε.le)
    (hAC (equilibriumCircleEmpiricalSupport_volume_zero z ε))
    (equilibriumCircleEmpirical_logEnergy_integrable hN z hε)
    (equilibriumCircleEmpirical_cross_integrable hN z hε hμnorm)
    (equilibriumObjective_finite_logEnergy_integrable hβ hG)

/-- Exact doubly smeared empirical self-energy, including the true circular
self-interactions. Repeated particle positions are allowed in this identity. -/
theorem equilibriumCircleEmpirical_selfEnergy {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumCircleEmpirical z ε).prod (equilibriumCircleEmpirical z ε)) =
      (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
        ∑ i : Fin N, ∑ j : Fin N, equilibriumDoubleCircularKernel ε (z i) (z j) := by
  have hi (p : Fin N × Fin N) := equilibriumCircle_logEnergy_integrable (z p.1) (z p.2) ε hε
  unfold equilibriumCircleEmpirical
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_sum,
    integral_smul_measure, integral_smul_measure,
    integral_sum_measure (integrable_sum_measure hi Summable.of_finite)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, tsum_fintype,
    Fintype.sum_prod_type, ← equilibriumDoubleCircularKernel_eq_energy hε]
  ring

/-- Exact empirical-reference cross energy. The single-circle cutoff appears
only in this cross term; positivity above uses the genuine double self-energy. -/
theorem equilibriumCircleEmpirical_crossEnergy {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hμ : Integrable (fun x : ℂ => ‖x‖) μ) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumCircleEmpirical z ε).prod μ) =
      (N : ℝ)⁻¹ * ∑ i : Fin N,
        ∫ y : ℂ, equilibriumCircularKernel ε (z i - y) ∂μ := by
  have hi (i : Fin N) : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleMeasure (z i) ε).prod μ) := by
    simpa only [Function.comp_def, Prod.swap, equilibriumLogKernel, norm_sub_rev] using
      (equilibriumMeasure_circle_logEnergy_integrable hμ (z i) hε).swap
  unfold equilibriumCircleEmpirical
  rw [Measure.prod_smul_left, Measure.prod_sum_left, integral_smul_measure,
    integral_sum_measure (integrable_sum_measure hi Summable.of_finite)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod _ (hi i)]
  rw [integral_integral_swap (hi i)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => equilibriumCircleMeasure_log_potential (z i) y hε)

end RepulsiveCoulomb
