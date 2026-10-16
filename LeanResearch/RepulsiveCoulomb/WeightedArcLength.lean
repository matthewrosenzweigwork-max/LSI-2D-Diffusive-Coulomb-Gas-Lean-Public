import LeanResearch.RepulsiveCoulomb.RealLineNormDet
import LeanResearch.RepulsiveCoulomb.Imported.ScalarCoarea.ScalarCoarea
import LeanResearch.RepulsiveCoulomb.PointWeightedPathArea
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Exact weighted Hausdorff length of an injective regular C1 arc, using the
approved lower-dimensional area formula and the proved one-dimensional Jacobian. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem fderiv_realLine_injective_of_deriv_ne_zero {γ : ℝ → ℂ} {x : ℝ}
    (hx : deriv γ x ≠ 0) : Function.Injective (fderiv ℝ γ x) := by
  rw [← toSpanSingleton_deriv]
  exact smul_left_injective ℝ hx

theorem weighted_hausdorff_length_regular_arc {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) {s t : ℝ} (hst : s < t)
    (hinj : InjOn γ (Icc s t)) (hreg : ∀ x ∈ Icc s t, deriv γ x ≠ 0)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in γ '' Icc s t, w z ∂(Measure.euclideanHausdorffMeasure 1)) =
      ∫⁻ x in Icc s t, ENNReal.ofReal ‖deriv γ x‖ * w (γ x) := by
  obtain ⟨C, hC⟩ := hγ.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc s t) isCompact_Icc
  have hd : ∀ x ∈ Icc s t, fderivWithin ℝ γ (Icc s t) x = fderiv ℝ γ x :=
    fun x hx => fderivWithin_eq_fderiv (uniqueDiffOn_Icc hst x hx) (hγ.differentiable one_ne_zero x)
  have hdi : ∀ᵐ x ∂volume.restrict (Icc s t), Function.Injective (fderivWithin ℝ γ (Icc s t) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [hd x hx]
    exact fderiv_realLine_injective_of_deriv_ne_zero (hreg x hx)
  have h := ProbabilityTheory.lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_lipschitzOnWith
    measurableSet_Icc hC hinj hdi w hw
  simp only [Module.finrank_self] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  change ENNReal.ofReal (fderivWithin ℝ γ (Icc s t) x).toLinearMap.normDet * w (γ x) = _
  rw [hd x hx, realLine_normDet_eq_norm_apply_one]
  rfl

theorem point_weighted_hausdorff_length_regular_arc {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) {s t : ℝ} (hst : s < t)
    (hinj : InjOn γ (Icc s t)) (hreg : ∀ x ∈ Icc s t, deriv γ x ≠ 0) :
    (∫⁻ z in γ '' Icc s t, ENNReal.ofReal (rawPointWeight a y z)
      ∂(Measure.euclideanHausdorffMeasure 1)) =
      ENNReal.ofReal (rawPointPathLength a y γ s t) := by
  rw [weighted_hausdorff_length_regular_arc hγ hst hinj hreg (fun z => ENNReal.ofReal (rawPointWeight a y z))
    (ENNReal.measurable_ofReal.comp (rawPointWeight_continuous ha y).measurable)]
  rw [← pointDoublePathELength_eq_rawPointPathLength ha y hγ hst.le]
  unfold pointConformalPathELength
  simp only [pointConformalDensity_double_exponents]
  apply lintegral_congr
  intro x
  exact mul_comm _ _

end RepulsiveCoulomb
