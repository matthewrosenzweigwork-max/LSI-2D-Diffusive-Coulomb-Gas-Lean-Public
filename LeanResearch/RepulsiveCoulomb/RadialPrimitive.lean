module

public import LeanResearch.RepulsiveCoulomb.PointConformalRadialBarrier
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! C1 radial primitives whose radial derivative vanishes near the center.
Their genuine Euclidean derivative is bounded by the nonnegative radial density. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def radialPrimitive (h : ℝ → ℝ) (c z : ℂ) : ℝ := ∫ t in (0 : ℝ)..‖z - c‖, h t

theorem continuous_primitive_contDiff (h : ℝ → ℝ) (hc : Continuous h) :
    ContDiff ℝ 1 (fun s : ℝ => ∫ t in (0 : ℝ)..s, h t) := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..s, h t) (h s) s :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hd s).differentiableAt, ?_⟩
  have he : deriv (fun s : ℝ => ∫ t in (0 : ℝ)..s, h t) = h := funext (fun s => (hd s).deriv)
  rw [he]
  exact hc

theorem radialPrimitive_eq_zero {h : ℝ → ℝ} {ε : ℝ} (hz : ∀ t ∈ Icc (0 : ℝ) ε, h t = 0)
    (c z : ℂ) (hd : ‖z - c‖ ≤ ε) : radialPrimitive h c z = 0 := by
  unfold radialPrimitive
  calc
    _ = ∫ t in (0 : ℝ)..‖z - c‖, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (norm_nonneg _)] at ht
      exact hz t ⟨ht.1, ht.2.trans hd⟩
    _ = 0 := by simp

theorem radialPrimitive_contDiff {h : ℝ → ℝ} (hc : Continuous h)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ t ∈ Icc (0 : ℝ) ε, h t = 0) (c : ℂ) :
    ContDiff ℝ 1 (radialPrimitive h c) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases he : z = c
  · subst z
    have heq : radialPrimitive h c =ᶠ[𝓝 c] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε : c ∈ ball c ε)] with w hw
      exact radialPrimitive_eq_zero hz c w (le_of_lt (by simpa [mem_ball, dist_eq_norm] using hw))
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact (continuous_primitive_contDiff h hc).contDiffAt.comp z
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr he))

theorem radialPrimitive_fderiv_le {h : ℝ → ℝ} (hc : Continuous h)
    (hn : ∀ t, 0 ≤ h t) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ t ∈ Icc (0 : ℝ) ε, h t = 0) (c z : ℂ) :
    ‖fderiv ℝ (radialPrimitive h c) z‖ ≤ h ‖z - c‖ := by
  by_cases he : z = c
  · subst z
    have heq : radialPrimitive h c =ᶠ[𝓝 c] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε : c ∈ ball c ε)] with w hw
      exact radialPrimitive_eq_zero hz c w (le_of_lt (by simpa [mem_ball, dist_eq_norm] using hw))
    rw [heq.fderiv_eq, fderiv_const_apply, norm_zero]
    exact hn _
  · let F : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, h t
    let N : ℂ → ℝ := fun w => ‖w - c‖
    have hF : HasDerivAt F (h (N z)) (N z) :=
      intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    have hN : DifferentiableAt ℝ N z :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr he)).differentiableAt one_ne_zero
    have hLip : LipschitzWith 1 N := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      simpa only [N, Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul, dist_eq_norm,
        sub_sub_sub_cancel_right] using abs_norm_sub_norm_le (u - c) (v - c)
    change ‖fderiv ℝ (F ∘ N) z‖ ≤ h (N z)
    rw [fderiv_comp z hF.differentiableAt hN]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [← norm_deriv_eq_norm_fderiv, hF.deriv, Real.norm_eq_abs, abs_of_nonneg (hn _)]
    have hb : ‖fderiv ℝ N z‖ ≤ 1 := norm_fderiv_le_of_lipschitz ℝ hLip
    nlinarith [hn (N z)]

end RepulsiveCoulomb
