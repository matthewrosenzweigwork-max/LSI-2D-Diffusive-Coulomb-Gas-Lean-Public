import LeanResearch.RepulsiveCoulomb.LocalRectifiability
import Mathlib.Analysis.Convex.Segment

/-! Exact invariance of metric variation under affine parametrization of an
unordered closed real interval by the unit interval. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem affine_unitInterval_image (a b : ℝ) :
    (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
  have h : (fun t : ℝ => a + t • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  simpa only [smul_eq_mul] using h

theorem eVariationOn_affine_unitInterval {X : Type*} [PseudoEMetricSpace X]
    (f : ℝ → X) (a b : ℝ) :
    eVariationOn (fun t : ℝ => f (a + t * (b - a))) (Icc (0 : ℝ) 1) =
      eVariationOn f (uIcc a b) := by
  let φ : ℝ → ℝ := fun t => a + t * (b - a)
  have him : φ '' Icc (0 : ℝ) 1 = uIcc a b := affine_unitInterval_image a b
  change eVariationOn (f ∘ φ) _ = _
  rcases le_total a b with hab | hba
  · have hm : MonotoneOn φ (Icc (0 : ℝ) 1) := by
      intro s _ t _ hst
      dsimp [φ]
      simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hab)) a
    rw [eVariationOn.comp_eq_of_monotoneOn f φ hm, him]
  · have hm : AntitoneOn φ (Icc (0 : ℝ) 1) := by
      intro s _ t _ hst
      dsimp [φ]
      simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonpos_right hst (sub_nonpos.mpr hba)) a
    rw [eVariationOn.comp_eq_of_antitoneOn f φ hm, him]

end RepulsiveCoulomb
