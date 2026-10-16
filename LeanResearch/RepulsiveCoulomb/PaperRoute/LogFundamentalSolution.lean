module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section

/-! The planar logarithmic fundamental solution against compact C2 tests.
The proof differentiates an explicit smooth regularization, integrates by parts
twice, computes exact rational peak mass, and takes the locally dominated limit.
All derivatives are actual real Fréchet derivatives, and the Laplacian is the
physical trace. The singular point is explicitly removed as a null set.
Only Mathlib is imported. No distributional or Green identity is assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set Module Bornology Metric
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

def logRegularization (ε : ℝ) (z : ℂ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (‖z‖ ^ 2 + ε ^ 2)

theorem logRegularization_denominator_pos {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    0 < ‖z‖ ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

theorem logRegularization_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (logRegularization ε) := by
  have hq : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  exact contDiff_const.mul (hq.log (fun z => ne_of_gt (logRegularization_denominator_pos hε z)))

theorem logRegularization_fderiv {ε : ℝ} (hε : 0 < ε) (z v : ℂ) :
    fderiv ℝ (logRegularization ε) z v =
      -(inner ℝ z v) / (‖z‖ ^ 2 + ε ^ 2) := by
  have hq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)
  have hlog := (hq.log (ne_of_gt (logRegularization_denominator_pos hε z))).const_mul
    (-(1 / 2 : ℝ))
  rw [show fderiv ℝ (logRegularization ε) z = _ from hlog.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- Directional second derivatives really are entries of the Fréchet Hessian. -/
theorem second_fderiv_apply_eq_iterated {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (z v w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ f x v) z w =
      iteratedFDeriv ℝ 2 f z ![w, v] := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) z) (differentiableAt_const v)]
  simp [iteratedFDeriv_two_apply]

theorem logRegularization_second_fderiv {ε : ℝ} (hε : 0 < ε) (z v w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ (logRegularization ε) x v) z w =
      -(inner ℝ w v) / (‖z‖ ^ 2 + ε ^ 2) +
      2 * inner ℝ z v * inner ℝ z w / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  have hq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)
  have hi := (hasDerivAt_inv (ne_of_gt (logRegularization_denominator_pos hε z))).comp_hasFDerivAt z hq
  have hn := ((innerSL ℝ v).hasFDerivAt (x := z)).neg
  have heq : (fun x => fderiv ℝ (logRegularization ε) x v) =
      (fun x => -(inner ℝ v x) * (‖x‖ ^ 2 + ε ^ 2)⁻¹) := by
    funext x
    rw [logRegularization_fderiv hε, real_inner_comm v x, div_eq_mul_inv]
  rw [heq]
  have hd := (hn.mul hi).fderiv
  change fderiv ℝ (fun x => -(inner ℝ v x) * (‖x‖ ^ 2 + ε ^ 2)⁻¹) z = _ at hd
  rw [hd]
  simp only [add_apply, smul_apply,
    neg_apply, innerSL_apply_apply, smul_eq_mul, Pi.neg_apply, Function.comp_apply]
  rw [real_inner_comm v z, real_inner_comm v w]
  ring

theorem logRegularization_laplacian {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Laplacian.laplacian (logRegularization ε) z =
      -2 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  have hf : ContDiff ℝ 2 (logRegularization ε) := (logRegularization_contDiff hε).of_le (by simp)
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [← second_fderiv_apply_eq_iterated hf, ← second_fderiv_apply_eq_iterated hf]
  rw [logRegularization_second_fderiv hε, logRegularization_second_fderiv hε]
  have hq := ne_of_gt (logRegularization_denominator_pos hε z)
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  rw [Complex.sq_norm] at hq ⊢
  simp only [Complex.normSq_apply] at hq ⊢
  field_simp
  ring

/-- Two ordinary integrations by parts, with every product integrable because
one factor is a compactly supported test function or its derivative. -/
theorem integral_mul_second_fderiv_eq {f φ : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    (∫ z, f z * fderiv ℝ (fun x => fderiv ℝ φ x v) z v) =
      ∫ z, fderiv ℝ (fun x => fderiv ℝ f x v) z v * φ z := by
  have hdf : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdφ : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hddf := (hdf.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := v))
  have hddφ := (hdφ.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := v))
  have hc1 := hφc.fderiv_apply ℝ v
  have hc2 := hc1.fderiv_apply ℝ v
  have hi1 := (hdf.continuous.mul hdφ.continuous).integrable_of_hasCompactSupport (μ := volume) hc1.mul_left
  have hi2 := (hf.continuous.mul hddφ).integrable_of_hasCompactSupport (μ := volume) hc2.mul_left
  have hi3 := (hf.continuous.mul hdφ.continuous).integrable_of_hasCompactSupport (μ := volume) hc1.mul_left
  have hi4 := (hddf.mul hφ.continuous).integrable_of_hasCompactSupport (μ := volume) hφc.mul_left
  have hi5 := (hdf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport (μ := volume) hφc.mul_left
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hdφ.differentiable (by norm_num) x)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi4 hi1 hi5
    (fun x _ => hdf.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)
  rw [hfirst, hsecond, neg_neg]

theorem laplacian_eq_second_fderiv {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Laplacian.laplacian φ = fun z =>
      fderiv ℝ (fun x => fderiv ℝ φ x 1) z 1 +
      fderiv ℝ (fun x => fderiv ℝ φ x Complex.I) z Complex.I := by
  funext z
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [second_fderiv_apply_eq_iterated hφ]

theorem continuous_laplacian_of_contDiff_two {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (Laplacian.laplacian φ) := by
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ (fun x => fderiv ℝ φ x v) z v) := by
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
      (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  rw [laplacian_eq_second_fderiv hφ]
  exact (hc 1).add (hc Complex.I)

theorem hasCompactSupport_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) : HasCompactSupport (Laplacian.laplacian φ) := by
  rw [laplacian_eq_second_fderiv hφ]
  exact ((hφc.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hφc.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I)

/-- The physical planar Laplacian is symmetric against a compact C2 test. -/
theorem integral_mul_laplacian_eq {f φ : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    (∫ z, f z * Laplacian.laplacian φ z) =
      ∫ z, Laplacian.laplacian f z * φ z := by
  have hc {g : ℂ → ℝ} (hg : ContDiff ℝ 2 g) (v : ℂ) :
      Continuous (fun z => fderiv ℝ (fun x => fderiv ℝ g x v) z v) := by
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ g x v) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi (v : ℂ) := (hf.continuous.mul (hc hφ v)).integrable_of_hasCompactSupport (μ := volume)
    ((hφc.fderiv_apply ℝ v).fderiv_apply ℝ v).mul_left
  have hj (v : ℂ) := ((hc hf v).mul hφ.continuous).integrable_of_hasCompactSupport (μ := volume) hφc.mul_left
  change ∀ v : ℂ, Integrable (fun z => f z * fderiv ℝ (fun x => fderiv ℝ φ x v) z v) at hi
  change ∀ v : ℂ, Integrable (fun z => fderiv ℝ (fun x => fderiv ℝ f x v) z v * φ z) at hj
  simp only [laplacian_eq_second_fderiv hf, laplacian_eq_second_fderiv hφ, mul_add, add_mul]
  rw [integral_add (hi 1) (hi Complex.I), integral_add (hj 1) (hj Complex.I),
    integral_mul_second_fderiv_eq hf hφ hφc 1,
    integral_mul_second_fderiv_eq hf hφ hφc Complex.I]

/-- Actual regularized test identity, including its Lebesgue integrability. -/
theorem logRegularization_integral_laplacian {ε : ℝ} (hε : 0 < ε)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => logRegularization ε z * Laplacian.laplacian φ z) ∧
    Integrable (fun z => (-2 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2) * φ z) ∧
    (∫ z, logRegularization ε z * Laplacian.laplacian φ z) =
      ∫ z, (-2 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2) * φ z := by
  have hf : ContDiff ℝ 2 (logRegularization ε) :=
    (logRegularization_contDiff hε).of_le (by simp)
  have hi := (hf.continuous.mul (continuous_laplacian_of_contDiff_two hφ)).integrable_of_hasCompactSupport (μ := volume)
    (hasCompactSupport_laplacian hφ hφc).mul_left
  have hj := ((continuous_laplacian_of_contDiff_two hf).mul hφ.continuous).integrable_of_hasCompactSupport (μ := volume)
    hφc.mul_left
  change Integrable (fun z => Laplacian.laplacian (logRegularization ε) z * φ z) at hj
  refine ⟨hi, ?_, ?_⟩
  · simpa only [Pi.mul_apply, logRegularization_laplacian hε] using hj
  · simpa only [logRegularization_laplacian hε] using integral_mul_laplacian_eq hf hφ hφc

def rationalKernel (z : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)

theorem rationalKernel_nonneg (z : ℂ) : 0 ≤ rationalKernel z := by
  unfold rationalKernel
  positivity

-- Exact radius integral, no planar PDE input.
theorem radial_integral :
    (∫ r : ℝ in Ioi 0, r / (1 + r ^ 2) ^ 2) = 1 / 2 := by
  let F : ℝ → ℝ := fun r => -((1 + r ^ 2)⁻¹) / 2
  have hd (r : ℝ) : HasDerivAt F (r / (1 + r ^ 2) ^ 2) r := by
    have hpos : 0 < 1 + r ^ 2 := by positivity
    have h := ((((hasDerivAt_id r).pow 2).const_add 1).inv hpos.ne').neg.div_const 2
    convert h using 1
    · rfl
    · dsimp
      field_simp
  have hsq : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
    tendsto_pow_atTop two_ne_zero
  have hsum : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 hsq
  have hf : Tendsto F atTop (𝓝 0) := by
    simpa only [F, Function.comp_apply, neg_zero, zero_div] using
      (tendsto_inv_atTop_zero.comp hsum).neg.div_const 2
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => hd r)
    (fun r (hr : r ∈ Ioi (0 : ℝ)) => div_nonneg hr.le (sq_nonneg _)) hf
  norm_num [F] at h ⊢
  exact h

theorem rationalKernel_integral : (∫ z : ℂ, rationalKernel z) = 1 := by
  change (∫ z : ℂ, (fun r : ℝ => 1 / (Real.pi * (1 + r ^ 2) ^ 2)) ‖z‖) = 1
  rw [integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ)
    (fun r : ℝ => 1 / (Real.pi * (1 + r ^ 2) ^ 2))]
  have he : (fun r : ℝ => r ^ (Module.finrank ℝ ℂ - 1) •
      (1 / (Real.pi * (1 + r ^ 2) ^ 2))) =
      (fun r : ℝ => Real.pi⁻¹ * (r / (1 + r ^ 2) ^ 2)) := by
    funext r
    simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
    field_simp
  rw [he, integral_const_mul, radial_integral]
  have hv : volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [Measure.real]
  rw [hv]
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat, nsmul_eq_mul, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

theorem rationalKernel_integrable : Integrable rationalKernel :=
  integrable_of_integral_eq_one rationalKernel_integral

-- Exact algebra reduces the rational decay to inverse-polynomial limits.
theorem rationalKernel_decay :
    Tendsto (fun z : ℂ => ‖z‖ ^ Module.finrank ℝ ℂ * rationalKernel z)
      (cobounded ℂ) (𝓝 0) := by
  have hsq : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (cobounded ℂ) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have hsum : Tendsto (fun z : ℂ => 1 + ‖z‖ ^ 2) (cobounded ℂ) atTop :=
    tendsto_atTop_add_const_left _ 1 hsq
  have hi : Tendsto (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsum
  have hlim := (hi.sub (hi.pow 2)).const_mul Real.pi⁻¹
  have he : (fun z : ℂ => ‖z‖ ^ Module.finrank ℝ ℂ * rationalKernel z) =
      (fun z : ℂ => Real.pi⁻¹ *
        ((1 + ‖z‖ ^ 2)⁻¹ - ((1 + ‖z‖ ^ 2)⁻¹) ^ 2)) := by
    funext z
    have hz : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
    simp only [Complex.finrank_real_complex, rationalKernel]
    field_simp [hz, Real.pi_ne_zero]
    ring
  rw [he]
  simpa only [zero_pow two_ne_zero, sub_zero, mul_zero] using hlim


/-- Algebraic scaling matches the regularization's physical Laplacian. -/
theorem logRegularization_laplacian_eq_scaled_peak {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Laplacian.laplacian (logRegularization c⁻¹) z =
      (-2 * Real.pi) * (c ^ 2 * rationalKernel (c • z)) := by
  rw [logRegularization_laplacian (inv_pos.mpr hc)]
  simp only [rationalKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hc0 := ne_of_gt hc
  have hq : ‖z‖ ^ 2 + c⁻¹ ^ 2 ≠ 0 :=
    ne_of_gt (logRegularization_denominator_pos (inv_pos.mpr hc) z)
  have hq' : 1 + (c * ‖z‖) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

def logRegularizationScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem logRegularizationScale_pos (n : ℕ) : 0 < logRegularizationScale n := by
  unfold logRegularizationScale
  positivity

theorem logRegularizationScale_le_one (n : ℕ) : logRegularizationScale n ≤ 1 := by
  unfold logRegularizationScale
  exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem logRegularizationScale_tendsto :
    Tendsto logRegularizationScale atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

/-- The rational peak has exact mass one and gives the expected delta limit. -/
theorem logRegularization_integral_laplacian_tendsto {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n : ℕ => ∫ z, logRegularization (logRegularizationScale n) z *
        Laplacian.laplacian φ z) atTop (𝓝 ((-2 * Real.pi) * φ 0)) := by
  have hiφ : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hp := tendsto_integral_comp_smul_smul_of_integrable rationalKernel_nonneg
    rationalKernel_integral rationalKernel_decay hiφ hφ.continuous.continuousAt
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hp' := (hp.comp hn).const_mul (-2 * Real.pi)
  convert hp' using 1
  funext n
  have hf : ContDiff ℝ 2 (logRegularization (logRegularizationScale n)) :=
    (logRegularization_contDiff (logRegularizationScale_pos n)).of_le (by simp)
  rw [integral_mul_laplacian_eq hf hφ hφc]
  simp only [logRegularizationScale, logRegularization_laplacian_eq_scaled_peak
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity), Complex.finrank_real_complex, smul_eq_mul, Function.comp_apply]
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-- Elementary local logarithmic integrability via the integrable planar 1/r
kernel on the unit disk. This is independent of equilibrium or force endpoints. -/
theorem logPositive_integrable :
    Integrable (fun z : ℂ => max (-Real.log ‖z‖) 0) := by
  have hi : Integrable (fun z : ℂ => if ‖z‖ < 1 then ‖z‖⁻¹ else 0) := by
    apply (integrable_fun_norm_addHaar (E := ℂ) (F := ℝ) (volume : Measure ℂ)
      (f := fun r : ℝ => if r < 1 then r⁻¹ else 0)).mpr
    have hi0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) volume :=
      integrableOn_const (by simp)
    have hi1 : Integrable ((Ioo 0 1).indicator (fun _ : ℝ => (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Ioo).mpr hi0
    apply hi1.integrableOn.congr
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with r hr
    have hr0 : 0 < r := hr
    by_cases hr1 : r < 1
    · simp [hr1, hr0, hr0.ne']
    · simp [hr1]
  apply hi.mono' (((Real.measurable_log.comp continuous_norm.measurable).neg).max
    measurable_const).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  change max (-Real.log ‖z‖) 0 ≤ (if ‖z‖ < 1 then ‖z‖⁻¹ else 0)
  by_cases hz : z = 0
  · subst z
    norm_num
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases h1 : ‖z‖ < 1
  · rw [ite_eq_left h1]
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hn)
    rw [Real.log_inv] at hl
    exact max_le (by linarith) (inv_nonneg.mpr hn.le)
  · rw [ite_eq_right h1]
    exact max_le (neg_nonpos.mpr (Real.log_nonneg (le_of_not_gt h1))) le_rfl

/-- Convergence is only asserted away from the logarithm's singular point. -/
theorem logRegularization_tendsto {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n => logRegularization (logRegularizationScale n) z) atTop
      (𝓝 (-Real.log ‖z‖)) := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hq : Tendsto (fun n => ‖z‖ ^ 2 + logRegularizationScale n ^ 2) atTop
      (𝓝 (‖z‖ ^ 2)) := by
    simpa using tendsto_const_nhds.add (logRegularizationScale_tendsto.pow 2)
  have hl := ((Real.continuousAt_log hn).tendsto.comp hq).const_mul (-(1 / 2 : ℝ))
  have he : -(1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) = -Real.log ‖z‖ := by
    rw [Real.log_pow]
    ring
  simpa only [logRegularization, Function.comp_apply, he] using hl

/-- The chosen finite value at zero has no effect on planar Lebesgue integrals. -/
theorem logKernel_zero_representative_ae (a : ℝ) :
    (fun z : ℂ => if z = 0 then a else -Real.log ‖z‖) =ᵐ[volume]
      (fun z : ℂ => -Real.log ‖z‖) := by
  filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℂ)] with z hz
  simp [hz]

-- Uniform scalar bound only off zero, exactly the condition used a.e. below.
theorem logRegularization_abs_bound_on_ball
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℂ}
    (hz : z ≠ 0) (hzR : ‖z‖ ≤ R) :
    |logRegularization ε z| ≤
      Real.log (R ^ 2 + 1) + max (-Real.log ‖z‖) 0 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hzR
  have hC : 0 ≤ Real.log (R ^ 2 + 1) := Real.log_nonneg (by nlinarith [sq_nonneg R])
  have hL : 0 ≤ max (-Real.log ‖z‖) 0 := le_max_right (-Real.log ‖z‖) 0
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hnormsq : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
  have hqpos := logRegularization_denominator_pos hε z
  have hlo := Real.log_le_log (sq_pos_of_pos hn)
    (show ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2 from le_add_of_nonneg_right (sq_nonneg ε))
  rw [Real.log_pow] at hlo
  norm_num only [Nat.cast_ofNat] at hlo
  have hhi := Real.log_le_log hqpos
    (show ‖z‖ ^ 2 + ε ^ 2 ≤ R ^ 2 + 1 by linarith)
  have hmax : -Real.log ‖z‖ ≤ max (-Real.log ‖z‖) 0 := le_max_left _ _
  unfold logRegularization
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Pairing convergence for any positive epsilon sequence tending to zero and bounded by one.
The actual n+1 inverse sequence is a direct specialization; see notes below. -/
theorem logRegularization_pairing_tendsto
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z => (-Real.log ‖z‖) * ψ z) ∧
    (∀ n, Integrable (fun z => logRegularization (ε n) z * ψ z)) ∧
    Tendsto (fun n => ∫ z, logRegularization (ε n) z * ψ z) atTop
      (𝓝 (∫ z, (-Real.log ‖z‖) * ψ z)) := by
  have hK : IsCompact (tsupport ψ) := hψc
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_closedBall_lt (1 : ℝ) (0 : ℂ)
  obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support hψc
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  let C : ℝ := Real.log (R ^ 2 + 1)
  have hC : 0 ≤ C := Real.log_nonneg (by nlinarith [sq_nonneg R])
  let S : Set ℂ := closedBall 0 R
  let bound : ℂ → ℝ := fun z => B * (S.indicator (fun _ => C) z + max (-Real.log ‖z‖) 0)
  have hCi : Integrable (S.indicator (fun _ : ℂ => C)) := by
    apply (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    exact integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  have hboundi : Integrable bound :=
    (hCi.add logPositive_integrable).const_mul B
  have hbound0 (z : ℂ) : 0 ≤ bound z := by
    unfold bound
    apply mul_nonneg hB0
    apply add_nonneg
    · exact Set.indicator_nonneg (fun _ _ => hC) z
    · exact le_max_right (-Real.log ‖z‖) 0
  have hpoint (z : ℂ) (hz : z ≠ 0) :
      Tendsto (fun n => logRegularization (ε n) z * ψ z) atTop
        (𝓝 ((-Real.log ‖z‖) * ψ z)) := by
    have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    have hq : Tendsto (fun n => ‖z‖ ^ 2 + ε n ^ 2) atTop (𝓝 (‖z‖ ^ 2)) := by
      simpa only [zero_pow two_ne_zero, add_zero] using tendsto_const_nhds.add (hεlim.pow 2)
    have hl := (Real.continuousAt_log hn).tendsto.comp hq
    have hp := (hl.const_mul (-(1 / 2 : ℝ))).mul_const (ψ z)
    have he : -(1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) = -Real.log ‖z‖ := by
      rw [Real.log_pow]
      ring
    simpa only [logRegularization, Function.comp_apply, he] using hp
  have hbn (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
      ‖logRegularization (ε n) z * ψ z‖ ≤ bound z := by
    by_cases hψz : ψ z = 0
    · simpa only [hψz, mul_zero, norm_zero] using hbound0 z
    · have hzK : z ∈ tsupport ψ := subset_tsupport ψ hψz
      have hzS : z ∈ S := hsub hzK
      have hzR : ‖z‖ ≤ R := by simpa only [S, mem_closedBall, dist_zero_right] using hzS
      have habs := logRegularization_abs_bound_on_ball (hε n) (hε1 n) hz hzR
      have habs' : ‖logRegularization (ε n) z‖ ≤ C + max (-Real.log ‖z‖) 0 := by
        simpa only [Real.norm_eq_abs] using habs
      rw [norm_mul]
      calc
        _ ≤ (C + max (-Real.log ‖z‖) 0) * ‖ψ z‖ :=
          mul_le_mul_of_nonneg_right habs' (norm_nonneg _)
        _ ≤ (C + max (-Real.log ‖z‖) 0) * B :=
          mul_le_mul_of_nonneg_left (hB z) (add_nonneg hC (le_max_right (-Real.log ‖z‖) 0))
        _ = bound z := by
          dsimp only [bound]
          rw [Set.indicator_of_mem hzS]
          ring
  have hb (n : ℕ) : ∀ᵐ z : ℂ, ‖logRegularization (ε n) z * ψ z‖ ≤ bound z := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact hbn n z hz
  have hlim : ∀ᵐ z : ℂ, Tendsto (fun n => logRegularization (ε n) z * ψ z) atTop
      (𝓝 ((-Real.log ‖z‖) * ψ z)) := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact hpoint z hz
  have htargetbound : ∀ᵐ z : ℂ, ‖(-Real.log ‖z‖) * ψ z‖ ≤ bound z := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact le_of_tendsto (hpoint z hz).norm (Eventually.of_forall (fun n => hbn n z hz))
  have htargeti : Integrable (fun z => (-Real.log ‖z‖) * ψ z) :=
    hboundi.mono' ((Real.measurable_log.comp continuous_norm.measurable).neg.mul hψ.measurable).aestronglyMeasurable htargetbound
  have hni (n : ℕ) : Integrable (fun z => logRegularization (ε n) z * ψ z) :=
    ((logRegularization_contDiff (hε n)).continuous.mul hψ).integrable_of_hasCompactSupport hψc.mul_left
  refine ⟨htargeti, hni, ?_⟩
  exact tendsto_integral_of_dominated_convergence bound
    (fun n => ((logRegularization_contDiff (hε n)).continuous.mul hψ).aestronglyMeasurable)
    hboundi hb hlim


/-- The actual planar logarithmic fundamental solution against every compact
C2 real test function, with both the physical Laplacian and genuine integrability.
This proves `-Δ(-log |z|) = 2π δ₀` in the test-function sense. -/
theorem log_fundamental_solution {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => (-Real.log ‖z‖) * Laplacian.laplacian φ z) ∧
    (∫ z, (-Real.log ‖z‖) * Laplacian.laplacian φ z) = (-2 * Real.pi) * φ 0 := by
  have hlimit := logRegularization_pairing_tendsto logRegularizationScale_pos
    logRegularizationScale_le_one logRegularizationScale_tendsto
    (continuous_laplacian_of_contDiff_two hφ) (hasCompactSupport_laplacian hφ hφc)
  exact ⟨hlimit.1, tendsto_nhds_unique hlimit.2.2
    (logRegularization_integral_laplacian_tendsto hφ hφc)⟩

/-- The distributional identity is unchanged by any finite representative at zero. -/
theorem log_fundamental_solution_zero_representative (a : ℝ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => (if z = 0 then a else -Real.log ‖z‖) * Laplacian.laplacian φ z) ∧
    (∫ z, (if z = 0 then a else -Real.log ‖z‖) * Laplacian.laplacian φ z) =
      (-2 * Real.pi) * φ 0 := by
  have he : (fun z => (if z = 0 then a else -Real.log ‖z‖) * Laplacian.laplacian φ z) =ᵐ[volume]
      (fun z => (-Real.log ‖z‖) * Laplacian.laplacian φ z) :=
    (logKernel_zero_representative_ae a).mul (Filter.EventuallyEq.refl _ _)
  obtain ⟨hi, hv⟩ := log_fundamental_solution hφ hφc
  exact ⟨hi.congr he.symm, (integral_congr_ae he).trans hv⟩

end RepulsiveCoulomb.PaperRoute
