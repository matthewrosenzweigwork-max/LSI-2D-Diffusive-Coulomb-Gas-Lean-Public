module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyDual
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-! Genuine monotone integral approximation by bounded scalar dual tests,
including infinite entropy. The AC case is linked to the pinned KL definition.
The singular-measure case and continuous-test approximation remain separate. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

theorem equilibriumEntropyDual_lintegral_tendsto (ν : Measure α) {q : α → ℝ}
    (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x) :
    Tendsto (fun n : ℕ => ∫⁻ x,
      ENNReal.ofReal (equilibriumEntropyDual (q x) (equilibriumClippedLog n (q x))) ∂ν) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (q x)) ∂ν)) := by
  have hm (n : ℕ) : Measurable (fun x =>
      equilibriumEntropyDual (q x) (equilibriumClippedLog n (q x))) := by
    have hc := (equilibriumClippedLog_measurable n).comp hqm
    exact ((hqm.mul hc).sub (Real.measurable_exp.comp hc)).add measurable_const
  apply lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hm n).ennreal_ofReal.aemeasurable)
  · exact Eventually.of_forall (fun x => by
      intro n m hnm
      exact ENNReal.ofReal_le_ofReal (equilibriumEntropyDual_clipped_monotone (hq0 x) hnm))
  · exact Eventually.of_forall (fun x =>
      (ENNReal.continuous_ofReal.tendsto _).comp (equilibriumEntropyDual_clipped_tendsto (hq0 x)))

/-- Actual approximation of KL for every absolutely continuous pair of finite
measures. There is no finite-entropy hypothesis; the limit may be infinity. -/
theorem equilibrium_klDiv_clipped_dual_tendsto {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    Tendsto (fun n : ℕ => ∫⁻ x,
      ENNReal.ofReal (equilibriumEntropyDual (μ.rnDeriv ν x).toReal
        (equilibriumClippedLog n (μ.rnDeriv ν x).toReal)) ∂ν) atTop
      (𝓝 (InformationTheory.klDiv μ ν)) := by
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hμν]
  exact equilibriumEntropyDual_lintegral_tendsto ν
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal (fun _ => ENNReal.toReal_nonneg)

end RepulsiveCoulomb
