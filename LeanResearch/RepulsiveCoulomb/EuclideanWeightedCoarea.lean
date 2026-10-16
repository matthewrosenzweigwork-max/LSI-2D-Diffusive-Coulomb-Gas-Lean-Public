import LeanResearch.RepulsiveCoulomb.Imported.ScalarCoarea.ScalarCoarea
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! The approved Asher Yan scalar coarea theorem, specialized to the actual real
Hilbert gradient and compactly supported C1 observables. No perimeter inequality
or level-set topology is assumed or concluded. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem euclidean_scalarJacobian_eq_gradient {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ProbabilityTheory.scalarJacobian f x = ENNReal.ofReal ‖gradient f x‖ := by
  simp [ProbabilityTheory.scalarJacobian, gradient]

theorem euclidean_weighted_coarea_compact_c1 {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal ‖gradient f x‖ * w x) =
      ∫⁻ t : ℝ, ∫⁻ x in f ⁻¹' {t}, w x
        ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf one_ne_zero
  have h := ProbabilityTheory.LipschitzWith.scalarCoareaFormula hC w hw
  simpa only [euclidean_scalarJacobian_eq_gradient, ProbabilityTheory.scalarCoareaFiber] using h

theorem euclidean_weighted_coarea_restrict_compact_c1 {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hw : Measurable w) {S : Set (EuclideanSpace ℝ (Fin d))} (hS : MeasurableSet S) :
    (∫⁻ x in S, ENNReal.ofReal ‖gradient f x‖ * w x) =
      ∫⁻ t : ℝ, ∫⁻ x in f ⁻¹' {t}, S.indicator w x
        ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
  have h := euclidean_weighted_coarea_compact_c1 hf hc (S.indicator w) (hw.indicator hS)
  rw [← h]
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ S <;> simp [hx]

end RepulsiveCoulomb
