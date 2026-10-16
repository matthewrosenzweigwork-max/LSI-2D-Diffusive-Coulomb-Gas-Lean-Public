import LeanResearch.RepulsiveCoulomb.ComplexWeightedCoarea
import LeanResearch.RepulsiveCoulomb.TriangularGridInterpolant

/-! Actual complex-plane coarea for globally Lipschitz functions, including the
constructed polygonal nodal interpolants. No C1 or regular-level hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace RepulsiveCoulomb

theorem complex_gradient_measurable (f : ℂ → ℝ) : Measurable (gradient f) := by
  change Measurable (fun z => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f z))
  exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem complex_weighted_coarea_lipschitz {f : ℂ → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z, ENNReal.ofReal ‖gradient f z‖ * w z) =
      ∫⁻ t : ℝ, ∫⁻ z in f ⁻¹' {t}, w z
        ∂(Measure.euclideanHausdorffMeasure 1) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hfc := hf.comp e.symm.lipschitz
  have hwc : Measurable (w ∘ e.symm) := hw.comp e.symm.continuous.measurable
  have h := ProbabilityTheory.LipschitzWith.scalarCoareaFormula hfc (w ∘ e.symm) hwc
  simp only [euclidean_scalarJacobian_eq_gradient, ProbabilityTheory.scalarCoareaFiber] at h
  have hv := Complex.orthonormalBasisOneI.measurePreserving_repr_symm
  have hg : Measurable (fun z => ENNReal.ofReal ‖gradient f z‖ * w z) :=
    (ENNReal.measurable_ofReal.comp (complex_gradient_measurable f).norm).mul hw
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

theorem complex_weighted_coarea_restrict_lipschitz {f : ℂ → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    {S : Set ℂ} (hS : MeasurableSet S) :
    (∫⁻ z in S, ENNReal.ofReal ‖gradient f z‖ * w z) =
      ∫⁻ t : ℝ, ∫⁻ z in S ∩ f ⁻¹' {t}, w z
        ∂(Measure.euclideanHausdorffMeasure 1) := by
  have h := complex_weighted_coarea_lipschitz hf (S.indicator w) (hw.indicator hS)
  have hl : (∫⁻ z, ENNReal.ofReal ‖gradient f z‖ * S.indicator w z) =
      ∫⁻ z in S, ENNReal.ofReal ‖gradient f z‖ * w z := by
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [hl] at h
  rw [h]
  apply lintegral_congr
  intro t
  rw [lintegral_indicator hS, Measure.restrict_restrict hS]

theorem triangularGridInterpolant_weighted_coarea (v : (ℤ × ℤ) →₀ ℝ)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) {S : Set ℂ} (hS : MeasurableSet S) :
    (∫⁻ z in S, ENNReal.ofReal ‖gradient (triangularGridInterpolant v) z‖ * w z) =
      ∫⁻ t : ℝ, ∫⁻ z in S ∩ (triangularGridInterpolant v) ⁻¹' {t}, w z
        ∂(Measure.euclideanHausdorffMeasure 1) :=
  complex_weighted_coarea_restrict_lipschitz (triangularGridInterpolant_lipschitz v) w hw hS

end RepulsiveCoulomb
