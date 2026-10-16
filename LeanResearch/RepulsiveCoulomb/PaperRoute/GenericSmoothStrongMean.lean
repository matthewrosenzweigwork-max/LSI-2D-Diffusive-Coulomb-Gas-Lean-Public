module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericSmoothStrongMedian
public import LeanResearch.RepulsiveCoulomb.MeanRpowCentering
public import LeanResearch.RepulsiveCoulomb.FiniteMeasureMedian

@[expose] public section

/-
Additive paper-route copy of the generic argument in SmoothStrongMean.lean.
Only the imports and namespace are rerouted; the physical-gradient statement
and the mathematical hypotheses are unchanged. The original file is untouched.
-/

/-! Complete mean-centered weak-to-strong upgrade for C1 functions with actual
finite inner moments. The weak estimate is quantified over all C1 truncations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

def universalSmoothTruncationConstant : ℝ := Classical.choose exists_smoothTransition_deriv_bound

theorem universalSmoothTruncationConstant_pos : 0 < universalSmoothTruncationConstant :=
  (Classical.choose_spec exists_smoothTransition_deriv_bound).1

theorem universalSmoothTruncationConstant_bound (t : ℝ) :
    ‖deriv Real.smoothTransition t‖ ≤ universalSmoothTruncationConstant :=
  (Classical.choose_spec exists_smoothTransition_deriv_bound).2 t

theorem smooth_weak_to_strong_mean (μ ν : Measure ℂ) [IsFiniteMeasure μ] [NeZero μ]
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hfi : Integrable f μ)
    (hb : ∃ L U : ℝ, ∀ᵐ x ∂μ, L ≤ f x ∧ f x ≤ U)
    {q κ K : ℝ} {W : ℝ≥0∞} (hq : 1 ≤ q) (hκ : 1 ≤ κ) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (hp : ∀ c : ℝ, Integrable (fun x => ‖f x - c‖ ^ q) μ)
    (hweak : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ q) * μ {x | t < ‖v x - (⨍ z, v z ∂μ)‖} ≤
        W * (∫⁻ x, ENNReal.ofReal (‖gradient v x‖ ^ 2) ∂ν) ^ κ) :
    (∫⁻ x, ENNReal.ofReal (‖f x - (⨍ z, f z ∂μ)‖ ^ q) ∂μ) ≤
      (2 * ENNReal.ofReal ((2 : ℝ) ^ q)) * (2 * ENNReal.ofReal ((16 : ℝ) ^ q)) * W *
        (ENNReal.ofReal (K ^ 2) * ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂ν) ^ κ := by
  obtain ⟨L, U, hbound⟩ := hb
  obtain ⟨c, hbelow, habove⟩ := exists_median_of_ae_bounded μ f hf.continuous.measurable hbound
  have hm := smooth_weak_to_strong_median μ ν hf c hbelow habove
    (lt_of_lt_of_le zero_lt_one hq) hκ hK0 hK hweak
  have h := (lintegral_rpow_mean_centering μ hf.continuous.measurable hfi c hq (hp c)).trans
    (mul_le_mul' le_rfl hm)
  simpa only [mul_assoc] using h

end RepulsiveCoulomb.PaperRoute
