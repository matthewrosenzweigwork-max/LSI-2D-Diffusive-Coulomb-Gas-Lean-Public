import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# A C1 logarithmic cutoff with actual planar Dirichlet energy

For every center `a : ℂ` and radii `0 < l < L`, the explicit cutoff
`cubicLogCutoff a l L` equals zero on the inner closed disk and one outside the
outer open disk. It is globally C1. Its actual real Fréchet derivative has
compact support in the closed annulus and square-integrable operator norm.
Its energy is bounded by `9 * π / (2 * log (L / l))`.

The scalar step is constructed by integrating the continuous slope
`max 0 (6*t*(1 - t))`; the fundamental theorem of calculus gives the actual
slope everywhere, and its middle branch is proved to be `3*t^2 - 2*t^3`.
The exact derivative-norm identity and the polar-coordinate annular kernel
integral establish the energy bound. No energy certificate is an input.

The cutoff itself is one at infinity: it is not asserted to have compact
support or to belong to global L2. This module imports only Mathlib and does
not prove the QC-to-weak-quasisymmetry or David–Semmes producers.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb.PaperRoute

/-- The compactly supported derivative of the clamped cubic step. -/
def cubicStepSlope (t : ℝ) : ℝ := max 0 (6 * t * (1 - t))

theorem continuous_cubicStepSlope : Continuous cubicStepSlope := by
  unfold cubicStepSlope
  fun_prop

theorem cubicStepSlope_nonneg (t : ℝ) : 0 ≤ cubicStepSlope t := le_max_left _ _

theorem cubicStepSlope_le (t : ℝ) : cubicStepSlope t ≤ 3 / 2 := by
  unfold cubicStepSlope
  apply max_le (by norm_num)
  nlinarith [sq_nonneg (t - 1 / 2)]

theorem cubicStepSlope_of_nonpos {t : ℝ} (ht : t ≤ 0) : cubicStepSlope t = 0 := by
  unfold cubicStepSlope
  rw [max_eq_left]
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) ht) (by linarith)

theorem cubicStepSlope_of_one_le {t : ℝ} (ht : 1 ≤ t) : cubicStepSlope t = 0 := by
  unfold cubicStepSlope
  rw [max_eq_left]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem cubicStepSlope_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cubicStepSlope t = 6 * t * (1 - t) := by
  unfold cubicStepSlope
  rw [max_eq_right]
  exact mul_nonneg (mul_nonneg (by norm_num) ht.1) (by linarith [ht.2])

/-- The cubic transition, obtained by integrating its actual continuous slope. -/
def cubicStep (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, cubicStepSlope u

theorem hasDerivAt_cubicStep (t : ℝ) : HasDerivAt cubicStep (cubicStepSlope t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_cubicStepSlope.intervalIntegrable _ _)
    continuous_cubicStepSlope.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_cubicStepSlope.continuousAt

theorem contDiff_cubicStep : ContDiff ℝ 1 cubicStep := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (hasDerivAt_cubicStep t).differentiableAt
  · have : deriv cubicStep = cubicStepSlope := funext fun t => (hasDerivAt_cubicStep t).deriv
    rw [this]
    exact continuous_cubicStepSlope

theorem cubicStep_of_nonpos {t : ℝ} (ht : t ≤ 0) : cubicStep t = 0 := by
  unfold cubicStep
  calc
    (∫ u in (0 : ℝ)..t, cubicStepSlope u) = ∫ _u in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact cubicStepSlope_of_nonpos ((uIcc_of_ge ht ▸ hu).2)
    _ = 0 := by simp

theorem cubicStep_polynomial {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cubicStep t = 3 * t ^ 2 - 2 * t ^ 3 := by
  unfold cubicStep
  have hp (u : ℝ) : HasDerivAt (fun v : ℝ => 3 * v ^ 2 - 2 * v ^ 3) (6 * u * (1 - u)) u := by
    convert (((hasDerivAt_id u).pow 2).const_mul 3).sub
      (((hasDerivAt_id u).pow 3).const_mul 2) using 1
    · ext v; simp
    · simp only [id_eq]; ring
  calc
    (∫ u in (0 : ℝ)..t, cubicStepSlope u) = ∫ u in (0 : ℝ)..t, 6 * u * (1 - u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      exact cubicStepSlope_of_mem_Icc ⟨hu.1, hu.2.trans ht.2⟩
    _ = (3 * t ^ 2 - 2 * t ^ 3) - (3 * (0 : ℝ)^2 - 2 * (0 : ℝ)^3) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · exact fun u _ => hp u
      · exact (by fun_prop : Continuous (fun u : ℝ => 6 * u * (1 - u))).intervalIntegrable _ _
    _ = 3 * t ^ 2 - 2 * t ^ 3 := by ring

theorem cubicStep_one : cubicStep 1 = 1 := by
  rw [cubicStep_polynomial (by simp)]
  norm_num

theorem cubicStep_of_one_le {t : ℝ} (ht : 1 ≤ t) : cubicStep t = 1 := by
  have hz : (∫ u in (1 : ℝ)..t, cubicStepSlope u) = 0 := by
    calc
      _ = ∫ _u in (1 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact cubicStepSlope_of_one_le ((uIcc_of_le ht ▸ hu).1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_cubicStepSlope.intervalIntegrable 0 1)
    (continuous_cubicStepSlope.intervalIntegrable 1 t)
  change cubicStep t = 1
  unfold cubicStep at *
  rw [← hsplit, hz, add_zero]
  exact cubicStep_one

theorem cubicStep_bounds (t : ℝ) : 0 ≤ cubicStep t ∧ cubicStep t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · rw [cubicStep_of_nonpos h0]; norm_num
  by_cases h1 : 1 ≤ t
  · rw [cubicStep_of_one_le h1]; norm_num
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_ge h0, le_of_not_ge h1⟩
  rw [cubicStep_polynomial ht]
  constructor
  · have h := mul_nonneg (sq_nonneg t) (show 0 ≤ 3 - 2 * t by linarith [ht.2])
    nlinarith
  · have h := mul_nonneg (sq_nonneg (1 - t)) (show 0 ≤ 1 + 2 * t by linarith [ht.1])
    nlinarith

/-- Width of the transition annulus in logarithmic coordinates. -/
def logAnnulusWidth (l L : ℝ) : ℝ := Real.log (L / l)

theorem logAnnulusWidth_pos {l L : ℝ} (hl : 0 < l) (hlL : l < L) :
    0 < logAnnulusWidth l L := by
  exact Real.log_pos ((one_lt_div hl).mpr hlL)

/-- The explicitly constructed C1 planar cutoff, zero at the inner disk and one at infinity. -/
def cubicLogCutoff (a : ℂ) (l L : ℝ) (z : ℂ) : ℝ :=
  cubicStep (Real.log (‖z - a‖ / l) / logAnnulusWidth l L)

theorem cubicLogCutoff_bounds (a : ℂ) (l L : ℝ) (z : ℂ) :
    0 ≤ cubicLogCutoff a l L z ∧ cubicLogCutoff a l L z ≤ 1 :=
  cubicStep_bounds _

theorem cubicLogCutoff_eq_zero {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hz : ‖z - a‖ ≤ l) : cubicLogCutoff a l L z = 0 := by
  apply cubicStep_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (logAnnulusWidth_pos hl hlL).le
  exact Real.log_nonpos (div_nonneg (norm_nonneg _) hl.le) ((div_le_one hl).mpr hz)

theorem cubicLogCutoff_eq_one {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hz : L ≤ ‖z - a‖) : cubicLogCutoff a l L z = 1 := by
  apply cubicStep_of_one_le
  apply (one_le_div (logAnnulusWidth_pos hl hlL)).mpr
  exact Real.log_le_log (div_pos (hl.trans hlL) hl) (div_le_div_of_nonneg_right hz hl.le)

theorem cubicLogCutoff_eventually_zero {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hz : ‖z - a‖ < l) :
    cubicLogCutoff a l L =ᶠ[𝓝 z] (fun _ => 0) := by
  have hcont : Continuous (fun w : ℂ => ‖w - a‖) := by fun_prop
  filter_upwards [hcont.continuousAt.eventually_lt_const hz] with w hw
  exact cubicLogCutoff_eq_zero hl hlL hw.le

theorem contDiff_cubicLogCutoff {a : ℂ} {l L : ℝ} (hl : 0 < l) (hlL : l < L) :
    ContDiff ℝ 1 (cubicLogCutoff a l L) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hza : z = a
  · apply contDiffAt_const.congr_of_eventuallyEq
    exact cubicLogCutoff_eventually_zero hl hlL (by simpa [hza] using hl)
  · have hn : ContDiffAt ℝ 1 (fun w : ℂ => ‖w - a‖) z :=
      (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hza)
    have hlog : ContDiffAt ℝ 1 (fun w : ℂ => Real.log (‖w - a‖ / l)) z :=
      (hn.div_const l).log (div_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)) hl.ne')
    exact contDiff_cubicStep.contDiffAt.comp z (hlog.div_const _)

theorem hasDerivAt_logRadius {r l L : ℝ} (hr : 0 < r) (hl : 0 < l) (_hlL : l < L) :
    HasDerivAt (fun s : ℝ => Real.log (s / l) / logAnnulusWidth l L)
      (1 / (logAnnulusWidth l L * r)) r := by
  convert (((hasDerivAt_id r).div_const l).log (div_ne_zero hr.ne' hl.ne')).div_const
    (logAnnulusWidth l L) using 1
  · rfl
  · simp only [id_eq]
    field_simp

theorem hasFDerivAt_cubicLogCutoff {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hza : z ≠ a) :
    HasFDerivAt (cubicLogCutoff a l L)
      ((cubicStepSlope (Real.log (‖z - a‖ / l) / logAnnulusWidth l L) /
        (logAnnulusWidth l L * ‖z - a‖)) • fderiv ℝ (fun w : ℂ => ‖w‖) (z - a)) z := by
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) (z - a) :=
    (contDiffAt_norm ℝ (sub_ne_zero.mpr hza)).differentiableAt one_ne_zero
  have hsub : HasFDerivAt (fun w : ℂ => ‖w - a‖)
      (fderiv ℝ (fun w : ℂ => ‖w‖) (z - a)) z := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using hn.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const a)
  unfold cubicLogCutoff
  have hscalar := (hasDerivAt_cubicStep _).comp ‖z - a‖
    (hasDerivAt_logRadius (norm_pos_iff.mpr (sub_ne_zero.mpr hza)) hl hlL)
  simpa only [Function.comp_def, mul_one_div] using hscalar.comp_hasFDerivAt z hsub

theorem fderiv_cubicLogCutoff_of_ne {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hza : z ≠ a) :
    fderiv ℝ (cubicLogCutoff a l L) z =
      (cubicStepSlope (Real.log (‖z - a‖ / l) / logAnnulusWidth l L) /
        (logAnnulusWidth l L * ‖z - a‖)) • fderiv ℝ (fun w : ℂ => ‖w‖) (z - a) :=
  (hasFDerivAt_cubicLogCutoff hl hlL hza).fderiv

theorem fderiv_cubicLogCutoff_center {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) : fderiv ℝ (cubicLogCutoff a l L) a = 0 := by
  have h := cubicLogCutoff_eventually_zero (a := a) (z := a) hl hlL (by simpa using hl)
  rw [h.fderiv_eq]
  simp

/-- Exact identity for the norm of the actual real Fréchet derivative, including the center. -/
theorem norm_fderiv_cubicLogCutoff {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    ‖fderiv ℝ (cubicLogCutoff a l L) z‖ =
      cubicStepSlope (Real.log (‖z - a‖ / l) / logAnnulusWidth l L) /
        (logAnnulusWidth l L * ‖z - a‖) := by
  by_cases hza : z = a
  · subst z
    simp [fderiv_cubicLogCutoff_center hl hlL]
  · rw [fderiv_cubicLogCutoff_of_ne hl hlL hza, norm_smul, norm_fderiv_norm]
    · rw [mul_one, Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (cubicStepSlope_nonneg _) (mul_nonneg (logAnnulusWidth_pos hl hlL).le (norm_nonneg _))
    · exact (contDiffAt_norm ℝ (sub_ne_zero.mpr hza)).differentiableAt one_ne_zero

theorem fderiv_cubicLogCutoff_eq_zero_of_le {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hz : ‖z - a‖ ≤ l) :
    fderiv ℝ (cubicLogCutoff a l L) z = 0 := by
  apply norm_eq_zero.mp
  rw [norm_fderiv_cubicLogCutoff hl hlL, cubicStepSlope_of_nonpos, zero_div]
  apply div_nonpos_of_nonpos_of_nonneg _ (logAnnulusWidth_pos hl hlL).le
  exact Real.log_nonpos (div_nonneg (norm_nonneg _) hl.le) ((div_le_one hl).mpr hz)

theorem fderiv_cubicLogCutoff_eq_zero_of_ge {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) (hz : L ≤ ‖z - a‖) :
    fderiv ℝ (cubicLogCutoff a l L) z = 0 := by
  apply norm_eq_zero.mp
  rw [norm_fderiv_cubicLogCutoff hl hlL, cubicStepSlope_of_one_le, zero_div]
  apply (one_le_div (logAnnulusWidth_pos hl hlL)).mpr
  exact Real.log_le_log (div_pos (hl.trans hlL) hl) (div_le_div_of_nonneg_right hz hl.le)

theorem support_fderiv_cubicLogCutoff_subset {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    Function.support (fderiv ℝ (cubicLogCutoff a l L)) ⊆
      {z : ℂ | l < ‖z - a‖ ∧ ‖z - a‖ < L} := by
  intro z hz
  constructor
  · by_contra h
    exact hz (fderiv_cubicLogCutoff_eq_zero_of_le hl hlL (le_of_not_gt h))
  · by_contra h
    exact hz (fderiv_cubicLogCutoff_eq_zero_of_ge hl hlL (le_of_not_gt h))

theorem tsupport_fderiv_cubicLogCutoff_subset {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    tsupport (fderiv ℝ (cubicLogCutoff a l L)) ⊆
      Metric.closedBall a L \ Metric.ball a l := by
  apply closure_minimal _ (Metric.isClosed_closedBall.inter Metric.isOpen_ball.isClosed_compl)
  intro z hz
  have h := support_fderiv_cubicLogCutoff_subset hl hlL hz
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using h.2.le,
    by simpa [Metric.mem_ball, dist_eq_norm] using not_lt.mpr h.1.le⟩

theorem hasCompactSupport_fderiv_cubicLogCutoff {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    HasCompactSupport (fderiv ℝ (cubicLogCutoff a l L)) := by
  exact ((isCompact_closedBall a L).diff Metric.isOpen_ball).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_fderiv_cubicLogCutoff_subset hl hlL)

theorem integrable_sq_norm_fderiv_cubicLogCutoff {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    Integrable (fun z : ℂ => ‖fderiv ℝ (cubicLogCutoff a l L) z‖ ^ 2) volume := by
  have hc : Continuous (fderiv ℝ (cubicLogCutoff a l L)) :=
    (contDiff_cubicLogCutoff (a := a) hl hlL).continuous_fderiv one_ne_zero
  have hs : HasCompactSupport (fderiv ℝ (cubicLogCutoff a l L)) :=
    hasCompactSupport_fderiv_cubicLogCutoff hl hlL
  have hs2 : HasCompactSupport ((fun d : ℂ →L[ℝ] ℝ => ‖d‖ ^ 2) ∘
      fderiv ℝ (cubicLogCutoff a l L)) := hs.comp_left (by simp)
  exact (hc.norm.pow 2).integrable_of_hasCompactSupport hs2

/-- The inverse-square radial kernel is integrable on every annulus away from its center. -/
theorem integrableOn_planarAnnularKernel (a : ℂ) {l L : ℝ} (hl : 0 < l) :
    IntegrableOn (fun z : ℂ => ‖z - a‖⁻¹ ^ 2)
      {z : ℂ | l < ‖z - a‖ ∧ ‖z - a‖ < L} := by
  let K : Set ℂ := closedBall a L \ ball a l
  have hK : IsCompact K := (isCompact_closedBall a L).diff isOpen_ball
  have hc : ContinuousOn (fun z : ℂ => ‖z - a‖⁻¹ ^ 2) K := by
    apply ContinuousOn.pow _ 2
    apply ContinuousOn.inv₀ ((continuous_id.sub continuous_const).norm.continuousOn)
    intro z hz
    have hz' : l ≤ ‖z - a‖ := by
      simpa only [mem_ball, dist_eq_norm, not_lt] using hz.2
    exact ne_of_gt (hl.trans_le hz')
  exact (hc.integrableOn_compact hK).mono_set (by
    intro z hz
    exact ⟨by simpa [mem_closedBall, dist_eq_norm] using hz.2.le,
      by simpa [mem_ball, dist_eq_norm] using not_lt.mpr hz.1.le⟩)

/-- Polar coordinates evaluate the origin-centered annular kernel with Jacobian `r`. -/
theorem integral_planarAnnularKernel_zero {l L : ℝ} (hl : 0 < l) (hL : l < L) :
    (∫ z : ℂ in {z | l < ‖z‖ ∧ ‖z‖ < L}, ‖z‖⁻¹ ^ 2) =
      2 * Real.pi * Real.log (L / l) := by
  let S : Set ℂ := {z | l < ‖z‖ ∧ ‖z‖ < L}
  let T : Set (ℝ × ℝ) := Ioo l L ×ˢ Ioo (-Real.pi) Real.pi
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hT : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : T ⊆ polarCoord.target := by
    intro p hp
    exact ⟨hl.trans hp.1.1, hp.2⟩
  rw [← integral_indicator hS, ← Complex.integral_comp_polarCoord_symm]
  calc
    (∫ p in polarCoord.target, p.1 • S.indicator (fun z => ‖z‖⁻¹ ^ 2)
        (Complex.polarCoord.symm p)) =
        ∫ p in polarCoord.target, T.indicator (fun p => p.1⁻¹) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      have hn := Complex.norm_polarCoord_symm p
      rw [abs_of_pos hp0] at hn
      by_cases h : l < p.1 ∧ p.1 < L
      · have hmem : Complex.polarCoord.symm p ∈ S := by simpa only [S, mem_ofPred_eq, hn] using h
        have htmem : p ∈ T := ⟨h, hp.2⟩
        simp only [indicator_of_mem hmem, indicator_of_mem htmem, hn,
          smul_eq_mul]
        field_simp
      · have hmem : Complex.polarCoord.symm p ∉ S := by simpa only [S, mem_ofPred_eq, hn] using h
        have htmem : p ∉ T := fun ht => h ht.1
        simp only [indicator_of_notMem hmem, indicator_of_notMem htmem, smul_zero]
    _ = ∫ p in T, p.1⁻¹ := by
      rw [setIntegral_indicator hT]
      rw [inter_eq_self_of_subset_right hsub]
    _ = (∫ r in Ioo l L, r⁻¹) * (∫ t in Ioo (-Real.pi) Real.pi, (1 : ℝ)) := by
      simpa [T, Measure.volume_eq_prod] using
        (setIntegral_prod_mul (μ := volume) (ν := volume) (fun r : ℝ => r⁻¹) (fun _ : ℝ => (1 : ℝ))
          (Ioo l L) (Ioo (-Real.pi) Real.pi))
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hL.le, integral_inv_of_pos hl (hl.trans hL)]
      simp [Real.pi_pos.le]
      ring

/-- Translation invariance gives the exact annular kernel integral at every center. -/
theorem integral_planarAnnularKernel (a : ℂ) {l L : ℝ} (hl : 0 < l) (hL : l < L) :
    (∫ z : ℂ in {z | l < ‖z - a‖ ∧ ‖z - a‖ < L}, ‖z - a‖⁻¹ ^ 2) =
      2 * Real.pi * Real.log (L / l) := by
  have hS : MeasurableSet {z : ℂ | l < ‖z - a‖ ∧ ‖z - a‖ < L} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  have hS0 : MeasurableSet {z : ℂ | l < ‖z‖ ∧ ‖z‖ < L} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  rw [← integral_indicator hS]
  calc
    _ = ∫ z : ℂ, ({z : ℂ | l < ‖z‖ ∧ ‖z‖ < L}.indicator
          (fun z => ‖z‖⁻¹ ^ 2)) (z - a) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [indicator_apply, mem_ofPred_eq]
    _ = ∫ z : ℂ, {z : ℂ | l < ‖z‖ ∧ ‖z‖ < L}.indicator
          (fun z => ‖z‖⁻¹ ^ 2) z := integral_sub_right_eq_self _ a
    _ = _ := by rw [integral_indicator hS0]; exact integral_planarAnnularKernel_zero hl hL

/-- Whole-plane integrability of the annular kernel extended by zero. -/
theorem integrable_planarAnnularKernel_indicator (a : ℂ) {l L : ℝ} (hl : 0 < l) :
    Integrable ({z : ℂ | l < ‖z - a‖ ∧ ‖z - a‖ < L}.indicator
      (fun z : ℂ => ‖z - a‖⁻¹ ^ 2)) := by
  apply (integrableOn_planarAnnularKernel a hl).integrable_indicator
  exact (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet


/-- The pointwise inverse-radius derivative estimate, with the actual derivative on the left. -/
theorem norm_fderiv_cubicLogCutoff_le {a z : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    ‖fderiv ℝ (cubicLogCutoff a l L) z‖ ≤ 3 / (2 * logAnnulusWidth l L * ‖z - a‖) := by
  rw [norm_fderiv_cubicLogCutoff hl hlL]
  calc
    _ ≤ (3 / 2) / (logAnnulusWidth l L * ‖z - a‖) :=
      div_le_div_of_nonneg_right (cubicStepSlope_le _)
        (mul_nonneg (logAnnulusWidth_pos hl hlL).le (norm_nonneg _))
    _ = _ := by ring

/-- Finite real Dirichlet energy of the explicit cubic logarithmic cutoff. -/
theorem integral_sq_norm_fderiv_cubicLogCutoff_le {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    (∫ z : ℂ, ‖fderiv ℝ (cubicLogCutoff a l L) z‖ ^ 2) ≤
      9 * Real.pi / (2 * Real.log (L / l)) := by
  let S : Set ℂ := {z | l < ‖z - a‖ ∧ ‖z - a‖ < L}
  let c : ℝ := 9 / (4 * logAnnulusWidth l L ^ 2)
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  have hbound (z : ℂ) : ‖fderiv ℝ (cubicLogCutoff a l L) z‖ ^ 2 ≤
      c * S.indicator (fun w : ℂ => ‖w - a‖⁻¹ ^ 2) z := by
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      calc
        _ ≤ (3 / (2 * logAnnulusWidth l L * ‖z - a‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_cubicLogCutoff_le hl hlL) 2
        _ = c * ‖z - a‖⁻¹ ^ 2 := by dsimp [c]; ring
    · have hd : fderiv ℝ (cubicLogCutoff a l L) z = 0 := by
        by_contra hd
        exact hz (support_fderiv_cubicLogCutoff_subset hl hlL hd)
      simp [hd, indicator_of_notMem hz]
  calc
    _ ≤ ∫ z : ℂ, c * S.indicator (fun w : ℂ => ‖w - a‖⁻¹ ^ 2) z :=
      integral_mono (integrable_sq_norm_fderiv_cubicLogCutoff hl hlL)
        ((integrable_planarAnnularKernel_indicator a hl).const_mul c) hbound
    _ = c * (2 * Real.pi * Real.log (L / l)) := by
      rw [integral_const_mul, integral_indicator hS, integral_planarAnnularKernel a hl hlL]
    _ = _ := by
      dsimp [c, logAnnulusWidth]
      field_simp [(logAnnulusWidth_pos hl hlL).ne']
      ring

/-- Nonnegative-integral energy form, suitable for a forward area formula. -/
theorem lintegral_sq_norm_fderiv_cubicLogCutoff_le {a : ℂ} {l L : ℝ}
    (hl : 0 < l) (hlL : l < L) :
    (∫⁻ z : ℂ, ENNReal.ofReal (‖fderiv ℝ (cubicLogCutoff a l L) z‖ ^ 2)) ≤
      ENNReal.ofReal (9 * Real.pi / (2 * Real.log (L / l))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_sq_norm_fderiv_cubicLogCutoff hl hlL)
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (integral_sq_norm_fderiv_cubicLogCutoff_le hl hlL)

/-- A genuine global C1 cutoff with zero/one plateaux and finite actual planar Dirichlet energy.
Only its derivative has compact support; the cutoff is one outside the outer disk. -/
theorem exists_planar_log_cutoff (a : ℂ) {l L : ℝ} (hl : 0 < l) (hlL : l < L) :
    ∃ ψ : ℂ → ℝ,
      ContDiff ℝ 1 ψ ∧
      (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧
      (∀ z, ‖z - a‖ ≤ l → ψ z = 0) ∧
      (∀ z, L ≤ ‖z - a‖ → ψ z = 1) ∧
      HasCompactSupport (fderiv ℝ ψ) ∧
      tsupport (fderiv ℝ ψ) ⊆ closedBall a L \ ball a l ∧
      Integrable (fun z => ‖fderiv ℝ ψ z‖ ^ 2) volume ∧
      (∫ z : ℂ, ‖fderiv ℝ ψ z‖ ^ 2) ≤ 9 * Real.pi / (2 * Real.log (L / l)) := by
  refine ⟨cubicLogCutoff a l L, contDiff_cubicLogCutoff hl hlL,
    cubicLogCutoff_bounds a l L, ?_, ?_, hasCompactSupport_fderiv_cubicLogCutoff hl hlL,
    tsupport_fderiv_cubicLogCutoff_subset hl hlL,
    integrable_sq_norm_fderiv_cubicLogCutoff hl hlL,
    integral_sq_norm_fderiv_cubicLogCutoff_le hl hlL⟩
  · exact fun _ hz => cubicLogCutoff_eq_zero hl hlL hz
  · exact fun _ hz => cubicLogCutoff_eq_one hl hlL hz

end RepulsiveCoulomb.PaperRoute
