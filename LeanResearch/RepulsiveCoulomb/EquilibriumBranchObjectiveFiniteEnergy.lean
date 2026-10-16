import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveDomain

/-! Finite objective implies the actual ordinary absolute energy integrability
needed for admissible variations. This is derived from the extended objective,
not assumed in a thermal-minimizer interface. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumObjective_finite_shiftedInteraction {β : ℝ} {μ : Measure ℂ}
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ) ≠ ∞ := by
  intro h
  have hc : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 := by norm_num
  have ht : ENNReal.ofReal (1 / 2 : ℝ) *
      (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ) ≤
        equilibriumNonnegativeObjective β μ := by
    exact (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)
  rw [h, ENNReal.mul_top hc] at ht
  exact hG (top_le_iff.mp ht)

/-- The true unregularized kernel is absolutely integrable under the actual
product reference once objective finiteness has been proved. -/
theorem equilibriumObjective_finite_logEnergy_integrable {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) (μ.prod μ) := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hG
  have hP2 := equilibriumObjective_finite_secondMoment hG
  letI : NullSingletonClass μ := ⟨fun x => hAC (measure_singleton x)⟩
  have hL := equilibriumLogMoment_measure_integrable hP2
  have hK := equilibriumObjective_finite_shiftedInteraction hG
  rw [lintegral_congr_ae (equilibriumExtendedKernel_ae_eq (μ := μ))] at hK
  have hm : Measurable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2) +
      equilibriumLogMoment p.1 + equilibriumLogMoment p.2) :=
    ((equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).add
      (equilibriumLogMoment_continuous.measurable.comp measurable_fst)).add
        (equilibriumLogMoment_continuous.measurable.comp measurable_snd)
  have hn : 0 ≤ᵐ[μ.prod μ] (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2) +
      equilibriumLogMoment p.1 + equilibriumLogMoment p.2) :=
    Eventually.of_forall (fun p => by
      change (0 : ℝ) ≤ equilibriumLogKernel (p.1 - p.2) + equilibriumLogMoment p.1 + equilibriumLogMoment p.2
      linarith [equilibriumLogKernel_sub_lower p.1 p.2])
  have hi := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).mp hK
  apply ((hi.sub (hL.comp_fst μ)).sub (hL.comp_snd μ)).congr
  exact Eventually.of_forall (fun p => by dsimp only [Pi.sub_apply]; ring)

/-- Actual absolute entropy integrability of the canonical Lebesgue density,
with finiteness derived from the objective rather than inserted as a hypothesis. -/
theorem equilibriumObjective_finite_entropy_integrable {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    Integrable (fun x : ℂ => equilibriumReferenceDensity μ x * Real.log (equilibriumReferenceDensity μ x)) := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ hG
  have hP2 := equilibriumObjective_finite_secondMoment hG
  have ha : 0 < β / 4 := by positivity
  have hKL := equilibriumObjective_finite_klDiv hβ hG
  have hE : equilibriumExtendedIntegral volume
      (fun x : ℂ => equilibriumReferenceDensity μ x * Real.log (equilibriumReferenceDensity μ x)) ≠ ⊤ := by
    rw [equilibriumReferenceEntropy_eq_gaussian_klDiv ha hAC hP2,
      ← EReal.coe_ennreal_toReal hKL, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  by_contra hi
  apply hE
  exact equilibriumExtendedIntegral_eq_top_of_not_integrable
    ((equilibriumReferenceDensity_measurable μ).mul
      (Real.measurable_log.comp (equilibriumReferenceDensity_measurable μ)))
    (equilibriumEntropyNegative_integrable ha (equilibriumReferenceDensity_measurable μ)
      (equilibriumReferenceDensity_nonneg μ) (equilibriumReferenceDensity_integrable μ)
      (equilibriumReferenceDensity_secondMoment_integrable hAC hP2)) hi

/-- The actual mean-field potential is integrable under the reference measure,
which is the side condition for multiplicative Euler--Lagrange variations. -/
theorem equilibriumObjective_finite_potential_integrable {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    Integrable (fun x : ℂ => ∫ y : ℂ, equilibriumLogKernel (x - y) ∂μ) μ :=
  (equilibriumObjective_finite_logEnergy_integrable hβ hG).integral_prod_left

end RepulsiveCoulomb
