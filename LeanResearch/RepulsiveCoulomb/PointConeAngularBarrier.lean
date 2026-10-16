module

public import LeanResearch.RepulsiveCoulomb.PointConeClippedCosine
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.OperatorNorm

@[expose] public section

/-! Angular support functions for identifying the singleton density metric with
the classical cone. The construction clips the developed angle at pi. -/
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem complex_abs_arg_eq_arccos {z : ℂ} (hz : z ≠ 0) :
    |Complex.arg z| = Real.arccos (z.re / ‖z‖) := by
  by_cases hi : 0 ≤ z.im
  · rw [abs_of_nonneg (Complex.arg_nonneg_iff.mpr hi), Complex.arg_of_im_nonneg_of_ne_zero hi hz]
  · have hi' : z.im < 0 := lt_of_not_ge hi
    rw [abs_of_neg (Complex.arg_neg_iff.mpr hi'), Complex.arg_of_im_neg hi', neg_neg]

theorem complex_abs_arg_continuousAt {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun w : ℂ ↦ |Complex.arg w|) z := by
  have he : (fun w : ℂ ↦ |Complex.arg w|) =ᶠ[𝓝 z] (fun w ↦ Real.arccos (w.re / ‖w‖)) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact complex_abs_arg_eq_arccos hw
  exact ((Real.continuous_arccos.continuousAt).comp
    (Complex.continuous_re.continuousAt.div continuousAt_id.norm (norm_ne_zero_iff.mpr hz))).congr_of_eventuallyEq he

theorem complex_arg_contDiffAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ 1 Complex.arg z := by
  have hlog : ContDiffAt ℝ 1 Complex.log z :=
    (Complex.contDiffAt_log hz (n := 1)).restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using Complex.imCLM.contDiff.contDiffAt.comp z hlog

def coneAngularBarrier (α : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ ^ (α + 1) / (α + 1)) * coneClippedCos ((α + 1) * Complex.arg z)

theorem coneAngularBarrier_abs_le {α : ℝ} (hα : 0 < α) (z : ℂ) :
    |coneAngularBarrier α z| ≤ ‖z‖ ^ (α + 1) / (α + 1) := by
  rw [coneAngularBarrier, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (coneClippedCos_abs_le_one _)

theorem coneAngularBarrier_zero {α : ℝ} (hα : 0 < α) : coneAngularBarrier α 0 = 0 := by
  simp [coneAngularBarrier, Real.zero_rpow (show α + 1 ≠ 0 by linarith)]

theorem coneAngularBarrier_eq_neg_radial {α : ℝ} {z : ℂ}
    (h : Real.pi ≤ |(α + 1) * Complex.arg z|) :
    coneAngularBarrier α z = -coneRadialPotential α z := by
  unfold coneAngularBarrier coneClippedCos coneRadialPotential
  by_cases ht : (α + 1) * Complex.arg z ∈ Icc (-Real.pi) Real.pi
  · have he : (α + 1) * Complex.arg z = -Real.pi ∨ (α + 1) * Complex.arg z = Real.pi := by
      rcases le_or_gt 0 ((α + 1) * Complex.arg z) with hp | hp
      · rw [abs_of_nonneg hp] at h
        exact Or.inr (le_antisymm ht.2 h)
      · rw [abs_of_neg hp] at h
        exact Or.inl (by linarith [ht.1])
    rcases he with he | he <;> simp [Set.piecewise, he, div_eq_mul_inv, mul_comm]
  · rw [piecewise_eq_of_notMem _ _ _ ht]
    ring

theorem coneAngularBarrier_contDiffAt_slit {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : ContDiffAt ℝ 1 (coneAngularBarrier α) z := by
  have hrad : ContDiffAt ℝ 1 (fun w : ℂ ↦ ‖w‖ ^ (α + 1) / (α + 1)) z :=
    (contDiff_norm_rpow (by linarith : (1 : ℝ) < α + 1)).contDiffAt.div_const _
  exact hrad.mul (coneClippedCos_contDiff.contDiffAt.comp z
    (contDiffAt_const.mul (complex_arg_contDiffAt hz)))

theorem coneAngularBarrier_eventually_neg_radial {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : z ≠ 0) (hangle : Real.pi < (α + 1) * |Complex.arg z|) :
    coneAngularBarrier α =ᶠ[𝓝 z] (fun w ↦ -coneRadialPotential α w) := by
  have hc : ContinuousAt (fun w : ℂ ↦ (α + 1) * |Complex.arg w|) z :=
    continuousAt_const.mul (complex_abs_arg_continuousAt hz)
  filter_upwards [hc.eventually (lt_mem_nhds hangle)] with w hw
  apply coneAngularBarrier_eq_neg_radial
  rw [abs_mul, abs_of_pos (by linarith : 0 < α + 1)]
  exact hw.le

theorem coneAngularBarrier_contDiffAt_ne_zero {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : z ≠ 0) : ContDiffAt ℝ 1 (coneAngularBarrier α) z := by
  by_cases hs : z ∈ Complex.slitPlane
  · exact coneAngularBarrier_contDiffAt_slit hα hs
  · have harg : Complex.arg z = Real.pi := by
      by_contra h
      exact hs (Complex.mem_slitPlane_iff_arg.mpr ⟨h, hz⟩)
    have hangle : Real.pi < (α + 1) * |Complex.arg z| := by
      rw [harg, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    exact (coneRadialPotential_contDiff hα).neg.contDiffAt.congr_of_eventuallyEq
      (coneAngularBarrier_eventually_neg_radial hα hz hangle)

theorem coneAngularBarrier_eq_sector_re {α : ℝ} {z : ℂ}
    (h : |(α + 1) * Complex.arg z| ≤ Real.pi) :
    coneAngularBarrier α z = (pointConeSectorMap α z).re := by
  have ht : (α + 1) * Complex.arg z ∈ Icc (-Real.pi) Real.pi := abs_le.mp h
  unfold coneAngularBarrier coneClippedCos
  rw [piecewise_eq_of_mem _ _ _ ht]
  simp only [pointConeSectorMap, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.cpow_ofReal_re]
  rw [mul_comm (Complex.arg z) (α + 1)]
  ring

theorem coneAngularBarrier_eventually_sector_re {α : ℝ} {z : ℂ}
    (hz : z ∈ Complex.slitPlane) (h : |(α + 1) * Complex.arg z| < Real.pi) :
    coneAngularBarrier α =ᶠ[𝓝 z] (fun w ↦ (pointConeSectorMap α w).re) := by
  have hc : ContinuousAt (fun w : ℂ ↦ |(α + 1) * Complex.arg w|) z :=
    (continuousAt_const.mul (Complex.continuousAt_arg hz)).abs
  filter_upwards [hc.eventually (gt_mem_nhds h)] with w hw
  exact coneAngularBarrier_eq_sector_re hw.le

theorem coneAngularBarrier_norm_fderiv_inner {α : ℝ} (hα : 0 < α) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) (h : |(α + 1) * Complex.arg z| < Real.pi) :
    ‖fderiv ℝ (coneAngularBarrier α) z‖ ≤ ‖z‖ ^ α := by
  have hF := (pointConeSectorMap_hasDerivAt hα.le hz).hasFDerivAt.restrictScalars ℝ
  have hRF := Complex.reCLM.hasFDerivAt.comp z hF
  have hb := hRF.congr_of_eventuallyEq (coneAngularBarrier_eventually_sector_re hz h)
  rw [hb.fderiv]
  calc
    _ ≤ ‖Complex.reCLM‖ * ‖(ContinuousLinearMap.toSpanSingleton ℂ (z ^ (α : ℂ))).restrictScalars ℝ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖z‖ ^ α := by
      rw [Complex.reCLM_norm, ContinuousLinearMap.norm_restrictScalars,
        ContinuousLinearMap.norm_toSpanSingleton, Complex.norm_cpow_real, one_mul]

end RepulsiveCoulomb
