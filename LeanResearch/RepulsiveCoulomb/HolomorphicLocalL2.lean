module

public import LeanResearch.RepulsiveCoulomb.HolomorphicDiskScaling
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

/-! Local holomorphic L2 evaluation, with no global continuity premise. -/
noncomputable section
open Set MeasureTheory Metric
namespace RepulsiveCoulomb

theorem holomorphic_local_disk_integral_lower {f : ℂ → ℂ} (c : ℂ) {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c (4 * r))) :
    (2 * Real.pi) * r ^ 2 * ‖f c‖ ^ 2 ≤ ∫ z in closedBall c (2 * r), ‖f z‖ ^ 2 := by
  let b : ContDiffBump c := ⟨2 * r, 3 * r, by positivity, by linarith⟩
  let g : ℂ → ℂ := fun z => b z • f z
  have hs : tsupport g ⊆ ball c (4 * r) := by
    apply (tsupport_smul_subset_left (b : ℂ → ℝ) f).trans
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [b]; linarith)
  have hc : Continuous g :=
    (b.continuous.continuousOn.smul hf.continuousOn).continuous_of_tsupport_subset isOpen_ball hs
  have he (z : ℂ) (hz : z ∈ closedBall c (2 * r)) : g z = f z := by
    have hb : b z = 1 := b.one_of_mem_closedBall hz
    simp only [g, hb, one_smul]
  have hd : DifferentiableOn ℂ g (ball c (2 * r)) := by
    apply (hf.mono (ball_subset_ball (by linarith : 2 * r ≤ 4 * r))).congr
    intro z hz
    exact he z (ball_subset_closedBall hz)
  have h := holomorphic_disk_integral_lower hc c hr hd
  have h0 : g c = f c := he c (mem_closedBall_self (by positivity))
  have hi : (∫ z in closedBall c (2 * r), ‖g z‖ ^ 2) =
      ∫ z in closedBall c (2 * r), ‖f z‖ ^ 2 := by
    apply setIntegral_congr_fun isClosed_closedBall.measurableSet
    intro z hz
    dsimp only
    rw [he z hz]
  simpa only [h0, hi] using h

end RepulsiveCoulomb
