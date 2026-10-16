module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.LogSmoothConvolution
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

/-! Actual exterior control of the literal logarithmic potential.
The physical logarithmic derivative is represented by complex inversion. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set Metric
open scoped Topology ContDiff Convolution
namespace RepulsiveCoulomb.PaperRoute

def planarLogDerivative (z : ℂ) : ℂ →L[ℝ] ℝ :=
  innerSL ℝ (-((starRingEnd ℂ) z⁻¹))

theorem planarLogDerivative_norm (z : ℂ) : ‖planarLogDerivative z‖ = ‖z‖⁻¹ := by
  simp [planarLogDerivative, innerSL_apply_norm]

theorem planarLogKernel_hasFDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt planarLogKernel (planarLogDerivative z) z := by
  have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt).log hn).const_mul (-(1 / 2 : ℝ))
  have he : planarLogKernel = fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w‖ ^ 2) := by
    funext w
    rw [Real.log_pow]
    unfold planarLogKernel
    ring
  rw [he]
  convert! h using 1
  ext v
  simp only [planarLogDerivative, innerSL_apply_apply, smul_apply, smul_eq_mul,
    Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.inv_re, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

theorem planarLogDerivative_locallyIntegrable : LocallyIntegrable planarLogDerivative volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by norm_num) (by norm_num)
  · filter_upwards [] with z
    rw [planarLogDerivative_norm, Real.rpow_neg_one, one_mul]
  · have hm : Measurable planarLogDerivative := by
      unfold planarLogDerivative
      fun_prop
    exact hm.aestronglyMeasurable

theorem planarLogDerivative_sub_norm {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖planarLogDerivative z - planarLogDerivative w‖ = ‖z - w‖ / (‖z‖ * ‖w‖) := by
  rw [planarLogDerivative, planarLogDerivative, ← map_sub, innerSL_apply_norm]
  rw [neg_sub_neg, ← map_sub, Complex.norm_conj, ← dist_eq_norm, dist_inv_inv₀ hw hz]
  rw [dist_eq_norm, norm_sub_rev, mul_comm]

/-- A lower bound on the entire closed ball used for the mean-value estimate. -/
theorem norm_ge_half_of_mem_half_ball {x z : ℂ} (hz : z ∈ closedBall x (‖x‖ / 2)) :
    ‖x‖ / 2 ≤ ‖z‖ := by
  have hd : ‖z - x‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have htri := norm_sub_le z x
  have ht : ‖x‖ ≤ ‖z‖ + ‖z - x‖ := by
    calc
      ‖x‖ = ‖z - (z - x)‖ := by congr 1; abel
      _ ≤ ‖z‖ + ‖z - x‖ := norm_sub_le _ _
  linarith

/-- Explicit exterior logarithmic oscillation. -/
theorem planarLogKernel_sub_bound {x y : ℂ} (hx : x ≠ 0) (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |planarLogKernel (x - y) - planarLogKernel x| ≤ 2 / ‖x‖ * ‖y‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnonzero (z : ℂ) (hz : z ∈ closedBall x (‖x‖ / 2)) : z ≠ 0 := by
    have hlow := norm_ge_half_of_mem_half_ball hz
    exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
  have hb (z : ℂ) (hz : z ∈ closedBall x (‖x‖ / 2)) :
      ‖fderiv ℝ planarLogKernel z‖ ≤ 2 / ‖x‖ := by
    rw [(planarLogKernel_hasFDerivAt (hnonzero z hz)).fderiv, planarLogDerivative_norm]
    have hlow := norm_ge_half_of_mem_half_ball hz
    have hzpos : 0 < ‖z‖ := by linarith
    rw [← one_div]
    apply (div_le_div_iff₀ hzpos hn).mpr
    linarith
  have h := (convex_closedBall x (‖x‖ / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (planarLogKernel_hasFDerivAt (hnonzero z hz)).differentiableAt) hb
    (mem_closedBall_self (by positivity)) (show x - y ∈ closedBall x (‖x‖ / 2) by
      simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hy)
  simpa only [Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] using h

/-- Explicit inverse-kernel cancellation estimate, including the physical operator norm. -/
theorem planarLogDerivative_sub_bound {x y : ℂ} (hx : x ≠ 0) (hy : ‖y‖ ≤ ‖x‖ / 2) :
    ‖planarLogDerivative (x - y) - planarLogDerivative x‖ ≤ 2 / ‖x‖ ^ 2 * ‖y‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmem : x - y ∈ closedBall x (‖x‖ / 2) := by
    simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hy
  have hlow := norm_ge_half_of_mem_half_ball hmem
  have hp : 0 < ‖x - y‖ := by linarith
  rw [planarLogDerivative_sub_norm (norm_pos_iff.mp hp) hx, sub_sub_cancel_left, norm_neg]
  apply (div_le_iff₀ (mul_pos hp hn)).mpr
  field_simp
  nlinarith [norm_nonneg y]

def smoothLogFirstMoment (η : ℂ → ℝ) : ℝ := ∫ y, ‖y‖ * |η y|

theorem smoothLogFirstMoment_integrable {η : ℂ → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) : Integrable (fun y => ‖y‖ * |η y|) := by
  have hi : Integrable (fun y : ℂ => ‖y‖ * ‖η y‖) :=
    (continuous_norm.mul hη.norm).integrable_of_hasCompactSupport hηc.norm.mul_left
  simpa only [Real.norm_eq_abs] using hi

theorem smoothLogFirstMoment_nonneg (η : ℂ → ℝ) : 0 ≤ smoothLogFirstMoment η :=
  integral_nonneg (fun y => mul_nonneg (norm_nonneg y) (abs_nonneg (η y)))

/-- Zero mass removes the nondecaying logarithmic term in the actual integral. -/
theorem smoothLogPotential_zero_mass_cancel {η : ℂ → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) (x : ℂ) :
    smoothLogPotential η x = ∫ y, (planarLogKernel (x - y) - planarLogKernel x) * η y := by
  have hiη : Integrable η := hη.integrable_of_hasCompactSupport hηc
  simp_rw [sub_mul]
  rw [integral_sub (smoothLogPotential_integrable_swap hη hηc x) (hiη.const_mul _),
    integral_const_mul, hmass, mul_zero, sub_zero, smoothLogPotential_eq_swap]

/-- Actual exterior potential estimate for a zero-mass compact source. -/
theorem smoothLogPotential_zero_mass_bound {η : ℂ → ℝ} {R : ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0)
    (hsupp : ∀ y ∈ tsupport η, ‖y‖ ≤ R) {x : ℂ} (hx : x ≠ 0) (hR : 2 * R ≤ ‖x‖) :
    |smoothLogPotential η x| ≤ 2 / ‖x‖ * smoothLogFirstMoment η := by
  rw [smoothLogPotential_zero_mass_cancel hη hηc hmass]
  have hi := (smoothLogFirstMoment_integrable hη hηc).const_mul (2 / ‖x‖)
  have hb : ∀ y, ‖(planarLogKernel (x - y) - planarLogKernel x) * η y‖ ≤
      2 / ‖x‖ * (‖y‖ * |η y|) := by
    intro y
    by_cases hy : η y = 0
    · simp [hy]
    have hs := hsupp y (subset_tsupport η hy)
    have he := planarLogKernel_sub_bound hx (show ‖y‖ ≤ ‖x‖ / 2 by linarith)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ (2 / ‖x‖ * ‖y‖) * |η y| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ = _ := by ring
  simpa only [Real.norm_eq_abs, integral_const_mul, smoothLogFirstMoment] using
    norm_integral_le_of_norm_le hi (Eventually.of_forall hb)

/-- The force row is genuinely integrable even before the exterior estimate. -/
theorem planarLogDerivative_row_integrable {η : ℂ → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) (x : ℂ) :
    Integrable (fun y => η y • planarLogDerivative (x - y)) := by
  have hi := hηc.convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ)).flip)
    planarLogDerivative_locallyIntegrable hη x
  have hi' := hi.comp_sub_left x
  simpa only [sub_sub_self, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] using hi'

/-- Outside the compact support, IBP moves the derivative to the explicit
logarithmic kernel. No differentiation across its singularity is used. -/
theorem smoothLogPotential_fderiv_eq_kernel_integral {η : ℂ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {x : ℂ}
    (hx : x ∉ tsupport η) :
    fderiv ℝ (smoothLogPotential η) x = ∫ y, η y • planarLogDerivative (x - y) := by
  have hiK := planarLogDerivative_row_integrable hη.continuous hηc x
  ext v
  rw [ContinuousLinearMap.integral_apply hiK, smoothLogPotential_fderiv hη hηc]
  change smoothLogPotential (fun z => fderiv ℝ η z v) x = _
  have hdc := (hη.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  have hid := smoothLogPotential_integrable_swap hdc (hηc.fderiv_apply ℝ v) x
  have hik : Integrable (fun y => (-(planarLogDerivative (x - y))) v * η y) := by
    have hi := (hiK.apply_continuousLinearMap v).neg
    convert! hi using 1
    ext y
    simp only [smul_apply, smul_eq_mul, neg_apply, Pi.neg_apply]
    ring
  have hibp := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := fun y => planarLogKernel (x - y))
    (f' := fun y => -(planarLogDerivative (x - y)))
    (g := η) (g' := fderiv ℝ η) (v := v) hik hid
    (smoothLogPotential_integrable_swap hη.continuous hηc x)
    (fun y hy => ?_) (fun y _ => (hη.differentiable one_ne_zero y).hasFDerivAt)
  · simp only [ContinuousLinearMap.mul_apply'] at hibp
    rw [smoothLogPotential_eq_swap]
    rw [hibp, ← integral_neg]
    congr 1
    ext y
    simp only [smul_apply, smul_eq_mul, neg_apply]
    ring
  · have hxy : x - y ≠ 0 := by
      intro he
      exact hx (sub_eq_zero.mp he ▸ hy)
    have hd := (planarLogKernel_hasFDerivAt hxy).comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    convert! hd using 1
    simp

/-- Zero mass cancels the constant physical force term. -/
theorem smoothLogPotential_fderiv_zero_mass_cancel {η : ℂ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0)
    {x : ℂ} (hx : x ∉ tsupport η) :
    fderiv ℝ (smoothLogPotential η) x =
      ∫ y, η y • (planarLogDerivative (x - y) - planarLogDerivative x) := by
  have hiη : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  rw [smoothLogPotential_fderiv_eq_kernel_integral hη hηc hx]
  simp_rw [smul_sub]
  rw [integral_sub (planarLogDerivative_row_integrable hη.continuous hηc x)
    (hiη.smul_const _), integral_smul_const, hmass, zero_smul, sub_zero]

/-- Actual zero-mass exterior derivative estimate; its constant is explicit. -/
theorem smoothLogPotential_fderiv_zero_mass_bound {η : ℂ → ℝ} {R : ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0)
    (hsupp : ∀ y ∈ tsupport η, ‖y‖ ≤ R) {x : ℂ} (hx : x ≠ 0) (hR : 2 * R ≤ ‖x‖) :
    ‖fderiv ℝ (smoothLogPotential η) x‖ ≤ 2 / ‖x‖ ^ 2 * smoothLogFirstMoment η := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxout : x ∉ tsupport η := by
    intro hs
    have := hsupp x hs
    linarith
  rw [smoothLogPotential_fderiv_zero_mass_cancel hη hηc hmass hxout]
  have hi := (smoothLogFirstMoment_integrable hη.continuous hηc).const_mul (2 / ‖x‖ ^ 2)
  have hb : ∀ y, ‖η y • (planarLogDerivative (x - y) - planarLogDerivative x)‖ ≤
      2 / ‖x‖ ^ 2 * (‖y‖ * |η y|) := by
    intro y
    by_cases hy : η y = 0
    · simp [hy]
    have hs := hsupp y (subset_tsupport η hy)
    have he := planarLogDerivative_sub_bound hx (show ‖y‖ ≤ ‖x‖ / 2 by linarith)
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |η y| * (2 / ‖x‖ ^ 2 * ‖y‖) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = _ := by ring
  simpa only [integral_const_mul, smoothLogFirstMoment] using
    norm_integral_le_of_norm_le hi (Eventually.of_forall hb)

/-- The normalized rational peak is an integrable majorant for the exterior
inverse-fourth-power energy tail. -/
theorem inverse_fourth_le_rationalKernel {x : ℂ} (hx : 1 ≤ ‖x‖) :
    (2 / ‖x‖ ^ 2) ^ 2 ≤ 16 * Real.pi * rationalKernel x := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hsq : 1 ≤ ‖x‖ ^ 2 := by nlinarith
  have hq : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [rationalKernel]
  have he : 16 * Real.pi * (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      16 / (1 + ‖x‖ ^ 2) ^ 2 := by field_simp
  rw [he, div_pow]
  apply (div_le_div_iff₀ (pow_pos (pow_pos hn 2) 2) (pow_pos hq 2)).mpr
  nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]

/-- Genuine global Dirichlet-energy integrability, proved before any unbounded
Green identity and using the actual zero-mass derivative decay. -/
theorem smoothLogPotential_energy_integrable {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hmass : (∫ y, η y) = 0) :
    Integrable (fun x => ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) := by
  obtain ⟨R, hR, hsupp⟩ := hηc.isBounded.exists_pos_norm_lt
  let S : ℝ := max (2 * R) 1
  let E : ℂ → ℝ := fun x => ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2
  have hc : Continuous E :=
    ((smoothLogPotential_contDiff (n := 2) hη hηc).continuous_fderiv (by norm_num)).norm.pow 2
  have hiB : Integrable ((closedBall (0 : ℂ) S).indicator E) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) S))
  have hi := hiB.add (rationalKernel_integrable.const_mul (16 * Real.pi * smoothLogFirstMoment η ^ 2))
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  change ‖E x‖ ≤ (closedBall (0 : ℂ) S).indicator E x +
    (16 * Real.pi * smoothLogFirstMoment η ^ 2) * rationalKernel x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hxB : x ∈ closedBall (0 : ℂ) S
  · rw [indicator_of_mem hxB]
    have : 0 ≤ (16 * Real.pi * smoothLogFirstMoment η ^ 2) * rationalKernel x :=
      mul_nonneg (by positivity) (rationalKernel_nonneg x)
    linarith
  · rw [indicator_of_notMem hxB, zero_add]
    have hxS : S < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hxB
    have hx1 : 1 ≤ ‖x‖ := (le_max_right _ _).trans hxS.le
    have hxR : 2 * R ≤ ‖x‖ := (le_max_left _ _).trans hxS.le
    have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hx1)
    have hb := smoothLogPotential_fderiv_zero_mass_bound (hη.of_le (by norm_num)) hηc hmass
      (fun y hy => (hsupp y hy).le) hx hxR
    have he : E x ≤ (2 / ‖x‖ ^ 2 * smoothLogFirstMoment η) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc
      E x ≤ (2 / ‖x‖ ^ 2 * smoothLogFirstMoment η) ^ 2 := he
      _ = (2 / ‖x‖ ^ 2) ^ 2 * smoothLogFirstMoment η ^ 2 := mul_pow _ _ _
      _ ≤ (16 * Real.pi * rationalKernel x) * smoothLogFirstMoment η ^ 2 :=
        mul_le_mul_of_nonneg_right (inverse_fourth_le_rationalKernel hx1) (sq_nonneg _)
      _ = _ := by ring

end RepulsiveCoulomb.PaperRoute
