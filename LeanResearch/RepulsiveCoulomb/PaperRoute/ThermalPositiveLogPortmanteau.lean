import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

/-! Bounded continuous positive-log truncations and their increasing supremum.
The extended kernel has true positive infinity on the diagonal. Weak lower
semicontinuity follows from actual product-measure bounded tests. -/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology BoundedContinuousFunction ENNReal
namespace RepulsiveCoulomb.PaperRoute

def thermalPositiveLogApprox (n : ℕ) (p : ℂ × ℂ) : ℝ :=
  max 0 (-Real.log (max (Real.exp (-(n : ℝ))) (dist p.1 p.2)))

def thermalExtendedPositiveLogKernel (p : ℂ × ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (thermalPositiveLogApprox n p)

def thermalPositiveLogInteraction (μ : ProbabilityMeasure ℂ) : ℝ≥0∞ :=
  ∫⁻ p, thermalExtendedPositiveLogKernel p ∂((μ : Measure ℂ).prod μ)

theorem thermalPositiveLogApprox_continuous (n : ℕ) :
    Continuous (thermalPositiveLogApprox n) := by
  unfold thermalPositiveLogApprox
  apply continuous_const.max
  apply Continuous.neg
  apply Continuous.log (continuous_const.max (continuous_fst.dist continuous_snd))
  intro p
  exact ne_of_gt ((Real.exp_pos (-(n : ℝ))).trans_le (le_max_left _ _))

theorem thermalPositiveLogApprox_nonneg (n : ℕ) (p : ℂ × ℂ) :
    0 ≤ thermalPositiveLogApprox n p := le_max_left _ _

theorem thermalPositiveLogApprox_le (n : ℕ) (p : ℂ × ℂ) :
    thermalPositiveLogApprox n p ≤ n := by
  have h := Real.log_le_log (Real.exp_pos (-(n : ℝ)))
    (le_max_left (Real.exp (-(n : ℝ))) (dist p.1 p.2))
  rw [Real.log_exp] at h
  exact max_le (Nat.cast_nonneg n) (by linarith)

theorem thermalPositiveLogApprox_monotone (p : ℂ × ℂ) :
    Monotone (fun n : ℕ => thermalPositiveLogApprox n p) := by
  intro n m hnm
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have he : Real.exp (-(m : ℝ)) ≤ Real.exp (-(n : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg hnmR)
  have hp : 0 < max (Real.exp (-(m : ℝ))) (dist p.1 p.2) :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hlog := Real.log_le_log hp (max_le_max_right (dist p.1 p.2) he)
  exact max_le_max le_rfl (neg_le_neg hlog)

def thermalPositiveLogBoundedApprox (n : ℕ) : (ℂ × ℂ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (thermalPositiveLogApprox n)
    (thermalPositiveLogApprox_continuous n) (n : ℝ) (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (thermalPositiveLogApprox_nonneg n p)]
      exact thermalPositiveLogApprox_le n p)

theorem thermalPositiveLogApprox_integrable (n : ℕ) (μ : ProbabilityMeasure (ℂ × ℂ)) :
    Integrable (thermalPositiveLogApprox n) (μ : Measure (ℂ × ℂ)) := by
  apply Integrable.of_bound (thermalPositiveLogApprox_continuous n).measurable.aestronglyMeasurable (n : ℝ)
  exact Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (thermalPositiveLogApprox_nonneg n p)]
    exact thermalPositiveLogApprox_le n p)

theorem thermalExtendedPositiveLogKernel_off_diagonal_dist {x y : ℂ} (hxy : x ≠ y) :
    thermalExtendedPositiveLogKernel (x, y) =
      ENNReal.ofReal (max (-Real.log (dist x y)) 0) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  apply le_antisymm
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    have hlog := Real.log_le_log hd
      (le_max_right (Real.exp (-(n : ℝ))) (dist x y))
    have h := max_le_max (le_refl (0 : ℝ)) (neg_le_neg hlog)
    simpa only [thermalPositiveLogApprox, max_comm] using h
  · obtain ⟨n, hn⟩ := exists_nat_ge (-Real.log (dist x y))
    have he : Real.exp (-(n : ℝ)) ≤ dist x y := by
      have h := Real.exp_le_exp.mpr (show -(n : ℝ) ≤ Real.log (dist x y) by linarith)
      simpa only [Real.exp_log hd] using h
    have hid : thermalPositiveLogApprox n (x, y) = max (-Real.log (dist x y)) 0 := by
      simp only [thermalPositiveLogApprox, max_eq_right he, max_comm]
    rw [← hid]
    exact le_iSup (fun m : ℕ => ENNReal.ofReal (thermalPositiveLogApprox m (x, y))) n

theorem thermalExtendedPositiveLogKernel_off_diagonal {x y : ℂ} (hxy : x ≠ y) :
    thermalExtendedPositiveLogKernel (x, y) =
      ENNReal.ofReal (max (-Real.log ‖x - y‖) 0) := by
  simpa only [dist_eq_norm] using thermalExtendedPositiveLogKernel_off_diagonal_dist hxy

theorem thermalPositiveLogApprox_diagonal (n : ℕ) (x : ℂ) :
    thermalPositiveLogApprox n (x, x) = n := by
  simp only [thermalPositiveLogApprox, dist_self,
    max_eq_left (Real.exp_pos _).le, Real.log_exp, neg_neg,
    max_eq_right (Nat.cast_nonneg n)]

theorem thermalExtendedPositiveLogKernel_diagonal (x : ℂ) :
    thermalExtendedPositiveLogKernel (x, x) = ∞ := by
  simp only [thermalExtendedPositiveLogKernel, thermalPositiveLogApprox_diagonal,
    ENNReal.ofReal_natCast, ENNReal.iSup_natCast]

theorem thermalExtendedPositiveLogKernel_measurable : Measurable thermalExtendedPositiveLogKernel :=
  Measurable.iSup (fun n => (thermalPositiveLogApprox_continuous n).measurable.ennreal_ofReal)

theorem thermalPositiveLogInteraction_eq_iSup (μ : ProbabilityMeasure ℂ) :
    thermalPositiveLogInteraction μ =
      ⨆ n : ℕ, ENNReal.ofReal
        (∫ p, thermalPositiveLogApprox n p ∂((μ : Measure ℂ).prod μ)) := by
  have hm (n : ℕ) : Measurable (fun p => ENNReal.ofReal (thermalPositiveLogApprox n p)) :=
    (thermalPositiveLogApprox_continuous n).measurable.ennreal_ofReal
  have hmono : Monotone (fun n : ℕ => fun p => ENNReal.ofReal (thermalPositiveLogApprox n p)) := by
    intro n m hnm p
    exact ENNReal.ofReal_le_ofReal (thermalPositiveLogApprox_monotone p hnm)
  unfold thermalPositiveLogInteraction thermalExtendedPositiveLogKernel
  rw [lintegral_iSup hm hmono]
  congr 1
  funext n
  exact (ofReal_integral_eq_lintegral_ofReal
    (thermalPositiveLogApprox_integrable n (μ.prod μ))
    (Eventually.of_forall (thermalPositiveLogApprox_nonneg n))).symm

/-- The singular positive interaction is weakly lower semicontinuous, including
infinite diagonal/positive energy. It is the supremum of genuine bounded-test
integrals; no shifted-kernel objective LSC is imported or assumed. -/
theorem thermalPositiveLogInteraction_lowerSemicontinuous :
    LowerSemicontinuous thermalPositiveLogInteraction := by
  have hp : Continuous (fun μ : ProbabilityMeasure ℂ => μ.prod μ) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have hi (n : ℕ) : Continuous (fun μ : ProbabilityMeasure ℂ =>
      ∫ p, thermalPositiveLogApprox n p ∂((μ : Measure ℂ).prod μ)) := by
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (thermalPositiveLogBoundedApprox n)).comp hp
  have he : thermalPositiveLogInteraction = (fun μ : ProbabilityMeasure ℂ =>
      ⨆ n : ℕ, ENNReal.ofReal
        (∫ p, thermalPositiveLogApprox n p ∂((μ : Measure ℂ).prod μ))) := by
    funext μ
    exact thermalPositiveLogInteraction_eq_iSup μ
  rw [he]
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp (hi n)).lowerSemicontinuous

end RepulsiveCoulomb.PaperRoute
