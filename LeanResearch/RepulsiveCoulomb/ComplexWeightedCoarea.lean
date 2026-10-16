import LeanResearch.RepulsiveCoulomb.EuclideanWeightedCoarea
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Isometric transport of actual scalar coarea to the complex plane with its
real physical gradient and Euclidean-normalized one-dimensional Hausdorff measure. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem complex_coarea_gradient_transport (f : ℂ → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖gradient (f ∘ Complex.orthonormalBasisOneI.repr.symm) x‖ =
      ‖gradient f (Complex.orthonormalBasisOneI.repr.symm x)‖ := by
  simp only [gradient, LinearIsometryEquiv.norm_map]
  change ‖fderiv ℝ (f ∘ (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) → ℂ)) x‖ = _
  rw [Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.comp_right_fderiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

theorem complex_weighted_coarea_compact_c1 {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z, ENNReal.ofReal ‖gradient f z‖ * w z) =
      ∫⁻ t : ℝ, ∫⁻ z in f ⁻¹' {t}, w z
        ∂(Measure.euclideanHausdorffMeasure 1) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hfc : ContDiff ℝ 1 (f ∘ e.symm) := hf.comp e.symm.toContinuousLinearEquiv.contDiff
  have hcc : HasCompactSupport (f ∘ e.symm) := hc.comp_homeomorph e.symm.toHomeomorph
  have hwc : Measurable (w ∘ e.symm) := hw.comp e.symm.continuous.measurable
  have h := euclidean_weighted_coarea_compact_c1 hfc hcc (w ∘ e.symm) hwc
  have hv := Complex.orthonormalBasisOneI.measurePreserving_repr_symm
  have hg : Measurable (fun z => ENNReal.ofReal ‖gradient f z‖ * w z) := by
    have hgc : Continuous (gradient f) :=
      (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
    exact (ENNReal.measurable_ofReal.comp hgc.norm.measurable).mul hw
  have hleft := hv.lintegral_comp hg
  have hright : (∫⁻ t : ℝ, ∫⁻ x in (f ∘ e.symm) ⁻¹' {t}, (w ∘ e.symm) x
      ∂(Measure.euclideanHausdorffMeasure (2 - 1))) =
      ∫⁻ t : ℝ, ∫⁻ z in f ⁻¹' {t}, w z ∂(Measure.euclideanHausdorffMeasure 1) := by
    apply lintegral_congr
    intro t
    have hm := e.symm.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure 1
    exact hm.setLIntegral_comp_preimage (hf.continuous.measurable (measurableSet_singleton t)) hw
  rw [← hright, ← h]
  simpa only [Function.comp_apply, e, complex_coarea_gradient_transport] using hleft.symm

end RepulsiveCoulomb
