module

public import LeanResearch.RepulsiveCoulomb.PointConeAngularBarrier

@[expose] public section

/-! The sharp physical derivative bound for the cone support profile. -/
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coneAngularBarrier_hasFDerivAt_outer {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) (h : Real.pi ≤ |(α + 1) * Complex.arg z|) :
    HasFDerivAt (coneAngularBarrier α) (-fderiv ℝ (coneRadialPotential α) z) z := by
  obtain ⟨hval, hder⟩ := coneClippedCos_outer_jet h
  have hargC : ContDiffAt ℝ 1 (fun w : ℂ ↦ (α + 1) * Complex.arg w) z :=
    contDiffAt_const.mul (complex_arg_contDiffAt hz)
  have harg := hargC.differentiableAt one_ne_zero
  have hH : HasFDerivAt (fun w : ℂ ↦ coneClippedCos ((α + 1) * Complex.arg w)) (0 : ℂ →L[ℝ] ℝ) z := by
    simpa [Function.comp_def] using hder.hasFDerivAt.comp z harg.hasFDerivAt
  have hrad := ((coneRadialPotential_contDiff hα).differentiable one_ne_zero z).hasFDerivAt
  have hp := hrad.mul hH
  have heq : coneAngularBarrier α =
      fun w ↦ coneRadialPotential α w * coneClippedCos ((α + 1) * Complex.arg w) := by
    funext w
    unfold coneAngularBarrier coneRadialPotential
    ring
  rw [heq]
  convert hp using 1
  simp [hval]

theorem coneAngularBarrier_norm_fderiv_ne_zero {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : z ≠ 0) : ‖fderiv ℝ (coneAngularBarrier α) z‖ ≤ ‖z‖ ^ α := by
  by_cases hs : z ∈ Complex.slitPlane
  · by_cases hin : |(α + 1) * Complex.arg z| < Real.pi
    · exact coneAngularBarrier_norm_fderiv_inner hα hs hin
    · rw [(coneAngularBarrier_hasFDerivAt_outer hα hs (le_of_not_gt hin)).fderiv, norm_neg,
        coneRadialPotential_norm_fderiv hα]
  · have harg : Complex.arg z = Real.pi := by
      by_contra h
      exact hs (Complex.mem_slitPlane_iff_arg.mpr ⟨h, hz⟩)
    have hangle : Real.pi < (α + 1) * |Complex.arg z| := by
      rw [harg, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    rw [(coneAngularBarrier_eventually_neg_radial hα hz hangle).fderiv_eq,
      fderiv_fun_neg, norm_neg, coneRadialPotential_norm_fderiv hα]

end RepulsiveCoulomb
