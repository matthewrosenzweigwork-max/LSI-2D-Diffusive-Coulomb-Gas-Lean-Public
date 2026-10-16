import LeanResearch.RepulsiveCoulomb.PointWeightAnnularNormalization
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-! Circle L2 submean inequality from actual holomorphic mean value and Jensen. -/
noncomputable section
open MeasureTheory Real Filter Set Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem circleAverage_norm_sq_ge (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) (h2 : CircleIntegrable (fun z => ‖f z‖ ^ 2) c R) :
    ‖Real.circleAverage f c R‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  have hμ : μ ≠ 0 := by
    intro h
    have hm := congrArg (fun ν : Measure ℝ => ν univ) h
    apply (ne_of_gt (ENNReal.ofReal_pos.mpr Real.two_pi_pos))
    simpa [μ] using hm
  letI : NeZero μ := ⟨hμ⟩
  have hc : ConvexOn ℝ (univ : Set ℂ) (fun z : ℂ => ‖z‖ ^ 2) := by
    convert! (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℂ))).pow
      (fun z _ => norm_nonneg z) 2 using 1
  have hj := hc.map_average_le (μ := μ) (f := fun θ => f (circleMap c R θ))
    (continuous_norm.pow 2).continuousOn isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) hf.1 h2.1
  simpa only [average_eq, μ, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal Real.two_pi_pos.le,
    Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le, Function.comp_def] using hj

theorem holomorphic_circle_norm_sq_lower {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) :
    ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  have hcl : closure (ball c R) = closedBall c R := by
    convert! (closure_ball (x := c) hR.ne') using 1
  have hc : ContinuousOn f (sphere c R) := hf.continuousOn.mono (by
    rw [hcl]
    exact sphere_subset_closedBall)
  have hm : Real.circleAverage f c R = f c := by
    apply DiffContOnCl.circleAverage
    simpa only [abs_of_pos hR] using hf
  have h := circleAverage_norm_sq_ge f c R
    (ContinuousOn.circleIntegrable hR.le hc)
    (ContinuousOn.circleIntegrable hR.le (hc.norm.pow 2))
  simpa only [hm] using h

end RepulsiveCoulomb
