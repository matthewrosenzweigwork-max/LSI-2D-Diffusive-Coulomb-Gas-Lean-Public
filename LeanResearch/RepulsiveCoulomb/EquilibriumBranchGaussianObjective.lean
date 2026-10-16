import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveDomain
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCrossInteraction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The actual normalized Gaussian has finite complete nonnegative objective.
In particular the product-space logarithmic energy is justified via the
literal withDensity product law, not merely an iterated default integral. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumGaussianProbability (a : ℝ) (ha : 0 < a) : ProbabilityMeasure ℂ :=
  ⟨equilibriumGaussianMeasure a, equilibriumGaussianMeasure_probability ha⟩

theorem equilibriumGaussianMeasure_secondMoment_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) (equilibriumGaussianMeasure a) :=
  (equilibriumDensityMeasure_integrable_iff (equilibriumGaussian_continuous a).measurable
    (fun x => (equilibriumGaussian_pos ha x).le) (fun x : ℂ => ‖x‖ ^ 2)).mpr
      (equilibriumGaussian_secondMoment_integrable ha)

theorem equilibriumGaussianMeasure_logEnergy_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumGaussianMeasure a).prod (equilibriumGaussianMeasure a)) := by
  have hm := (equilibriumGaussian_continuous a).measurable
  have h0 := fun x => (equilibriumGaussian_pos ha x).le
  have hi := equilibriumGaussian_integrable ha
  have hmass := integral_equilibriumGaussian ha
  have hL := equilibriumLogMoment_mul_integrable hm h0 hi (equilibriumGaussian_secondMoment_integrable ha)
  have hcross := equilibriumCrossInteraction_integrable hm h0 hi hL
    hm h0 (equilibriumGaussian_le ha) hi hmass hL
  unfold equilibriumGaussianMeasure equilibriumDensityMeasure
  rw [prod_withDensity hm.ennreal_ofReal hm.ennreal_ofReal]
  apply (integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))).mpr
  apply hcross.congr
  exact Eventually.of_forall (fun p => by
    dsimp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 p.1), ENNReal.toReal_ofReal (h0 p.2)]
    ring)

/-- Finiteness of the true extended shifted interaction of the Gaussian. -/
theorem equilibriumGaussianMeasure_shiftedEnergy_ne_top {a : ℝ} (ha : 0 < a) :
    (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p
      ∂(equilibriumGaussianMeasure a).prod (equilibriumGaussianMeasure a)) ≠ ∞ := by
  letI := equilibriumGaussianMeasure_probability ha
  letI : NullSingletonClass (equilibriumGaussianMeasure a) := by
    unfold equilibriumGaussianMeasure equilibriumDensityMeasure
    infer_instance
  have hP2 := equilibriumGaussianMeasure_secondMoment_integrable ha
  have hL := equilibriumLogMoment_measure_integrable hP2
  have hs := ((equilibriumGaussianMeasure_logEnergy_integrable ha).add
    (hL.comp_fst (equilibriumGaussianMeasure a))).add (hL.comp_snd (equilibriumGaussianMeasure a))
  have hn : 0 ≤ᵐ[(equilibriumGaussianMeasure a).prod (equilibriumGaussianMeasure a)]
      (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2) +
        equilibriumLogMoment p.1 + equilibriumLogMoment p.2) :=
    Eventually.of_forall (fun p => by
      change (0 : ℝ) ≤ equilibriumLogKernel (p.1 - p.2) + equilibriumLogMoment p.1 + equilibriumLogMoment p.2
      linarith [equilibriumLogKernel_sub_lower p.1 p.2])
  rw [lintegral_congr_ae (equilibriumExtendedKernel_ae_eq (μ := equilibriumGaussianMeasure a))]
  exact (lintegral_ofReal_ne_top_iff_integrable hs.aestronglyMeasurable hn).mpr hs

/-- Finite complete objective for the actual beta/4 Gaussian, for every beta>0. -/
theorem equilibriumGaussianObjective_ne_top {β : ℝ} (hβ : 0 < β) :
    equilibriumNonnegativeObjective β (equilibriumGaussianMeasure (β / 4)) ≠ ∞ := by
  have ha : 0 < β / 4 := by positivity
  letI := equilibriumGaussianMeasure_probability ha
  have hK := equilibriumGaussianMeasure_shiftedEnergy_ne_top ha
  have hP2 := equilibriumGaussianMeasure_secondMoment_integrable ha
  have hW : (∫⁻ x : ℂ, ENNReal.ofReal (equilibriumShiftedConfinement x)
      ∂equilibriumGaussianMeasure (β / 4)) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable
      equilibriumShiftedConfinement_continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall equilibriumShiftedConfinement_nonneg)).mpr
        (equilibriumShiftedConfinement_integrable hP2)
  unfold equilibriumNonnegativeObjective
  rw [InformationTheory.klDiv_self]
  finiteness

end RepulsiveCoulomb
