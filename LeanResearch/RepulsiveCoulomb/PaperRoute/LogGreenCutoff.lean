import LeanResearch.RepulsiveCoulomb.PaperRoute.LogSmoothConvolution
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Complex.Basic

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace RepulsiveCoulomb.PaperRoute

def planarFunctionalVector (L : ℂ →L[ℝ] ℝ) : ℂ := ⟨L 1, L Complex.I⟩

theorem planarFunctional_eq_innerSL (L : ℂ →L[ℝ] ℝ) :
    L = innerSL ℝ (planarFunctionalVector L) := by
  ext z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  have he : L z = z.re * L 1 + z.im * L Complex.I := by
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [he]
  simp only [innerSL_apply_apply, Complex.inner, planarFunctionalVector,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem planarFunctionalVector_norm (L : ℂ →L[ℝ] ℝ) :
    ‖planarFunctionalVector L‖ = ‖L‖ := by
  conv_rhs => rw [planarFunctional_eq_innerSL L]
  rw [innerSL_apply_norm]

theorem planarFunctional_norm_sq (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = (L 1)^2 + (L Complex.I)^2 := by
  rw [← planarFunctionalVector_norm L, Complex.sq_norm]
  simp only [planarFunctionalVector, Complex.normSq_apply]
  ring

theorem planarFunctional_dot_bound (L M : ℂ →L[ℝ] ℝ) :
    |L 1 * M 1 + L Complex.I * M Complex.I| ≤ ‖L‖ * ‖M‖ := by
  have h := abs_real_inner_le_norm (planarFunctionalVector L) (planarFunctionalVector M)
  rw [planarFunctionalVector_norm, planarFunctionalVector_norm] at h
  simpa only [Complex.inner, planarFunctionalVector, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add, mul_comm] using h

/-- One physical directional component of the compact-cutoff Green identity.
Every product required by IBP is genuinely integrable via compact support. -/
theorem logGreen_cutoff_direction {h χ : ℂ → ℝ}
    (hh : ContDiff ℝ 2 h) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (v : ℂ) :
    (∫ x : ℂ, χ x ^ 2 * h x *
      fderiv ℝ (fun y => fderiv ℝ h y v) x v) =
      -(∫ x : ℂ, χ x ^ 2 * (fderiv ℝ h x v)^2 +
        2 * χ x * h x * fderiv ℝ χ x v * fderiv ℝ h x v) := by
  let q : ℂ → ℝ := fun x => h x * χ x * χ x
  let d : ℂ → ℝ := fun x => fderiv ℝ h x v
  have hq : ContDiff ℝ 2 q := (hh.mul hχ).mul hχ
  have hqc : HasCompactSupport q := by
    exact hχc.mul_left
  have hd : ContDiff ℝ 1 d :=
    (hh.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hDq : Continuous (fun x => fderiv ℝ q x v) :=
    (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDd : Continuous (fun x => fderiv ℝ d x v) :=
    (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ q x v * d x) :=
    (hDq.mul hd.continuous).integrable_of_hasCompactSupport
      (μ := volume) (hqc.fderiv_apply ℝ v).mul_right
  have hi2 : Integrable (fun x => q x * fderiv ℝ d x v) :=
    (hq.continuous.mul hDd).integrable_of_hasCompactSupport
      (μ := volume) hqc.mul_right
  have hi3 : Integrable (fun x => q x * d x) :=
    (hq.continuous.mul hd.continuous).integrable_of_hasCompactSupport
      (μ := volume) hqc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := v) hi1 hi2 hi3
    (fun x _ => hq.differentiable (by norm_num) x)
    (fun x _ => hd.differentiable (by norm_num) x)
  have heq (x : ℂ) : fderiv ℝ q x v * d x =
      χ x ^ 2 * (fderiv ℝ h x v)^2 +
        2 * χ x * h x * fderiv ℝ χ x v * fderiv ℝ h x v := by
    have Hh := (hh.differentiable (by norm_num) x).hasFDerivAt
    have Hχ := (hχ.differentiable (by norm_num) x).hasFDerivAt
    have Hq : HasFDerivAt q
        ((h x * χ x) • fderiv ℝ χ x +
          χ x • (h x • fderiv ℝ χ x + χ x • fderiv ℝ h x)) x :=
      (Hh.mul Hχ).mul Hχ
    rw [Hq.fderiv]
    simp only [add_apply, smul_apply,
      smul_eq_mul, d]
    ring
  calc
    (∫ x : ℂ, χ x ^ 2 * h x *
      fderiv ℝ (fun y => fderiv ℝ h y v) x v) =
        ∫ x : ℂ, q x * fderiv ℝ d x v := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [q, d]
      ring
    _ = -(∫ x : ℂ, fderiv ℝ q x v * d x) := hibp
    _ = _ := congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall heq))


/-- The genuine compact-cutoff Green identity with the physical gradient norm.
No global energy integrability or boundary limit is assumed here. -/
theorem logGreen_cutoff_identity {h χ : ℂ → ℝ}
    (hh : ContDiff ℝ 2 h) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * ‖fderiv ℝ h x‖ ^ 2) =
      -(∫ x, χ x ^ 2 * h x * Laplacian.laplacian h x) -
      2 * (∫ x, χ x * h x * (fderiv ℝ χ x 1 * fderiv ℝ h x 1 +
        fderiv ℝ χ x Complex.I * fderiv ℝ h x Complex.I)) := by
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have hχdc : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by norm_num)
  have hd (v : ℂ) := hdc.clm_apply (continuous_const (y := v))
  have hχd (v : ℂ) := hχdc.clm_apply (continuous_const (y := v))
  have hdd (v : ℂ) : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ h y v) x v) := by
    have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ h y v) :=
      (hh.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hc2 : HasCompactSupport (fun x => χ x ^ 2) := by
    simp only [pow_two]
    exact hχc.mul_right
  have hiL (v : ℂ) : Integrable (fun x => χ x ^ 2 * h x *
      fderiv ℝ (fun y => fderiv ℝ h y v) x v) :=
    (((hχ.continuous.pow 2).mul hh.continuous).mul (hdd v)).integrable_of_hasCompactSupport
      (hc2.mul_right.mul_right)
  have hiR (v : ℂ) : Integrable (fun x => χ x ^ 2 * (fderiv ℝ h x v) ^ 2 +
      2 * χ x * h x * fderiv ℝ χ x v * fderiv ℝ h x v) := by
    have hiA : Integrable (fun x => χ x ^ 2 * (fderiv ℝ h x v) ^ 2) :=
      ((hχ.continuous.pow 2).mul ((hd v).pow 2)).integrable_of_hasCompactSupport hc2.mul_right
    have hiB : Integrable (fun x => 2 * χ x * h x * fderiv ℝ χ x v * fderiv ℝ h x v) :=
      ((((continuous_const.mul hχ.continuous).mul hh.continuous).mul (hχd v)).mul (hd v)).integrable_of_hasCompactSupport
        hχc.mul_left.mul_right.mul_right.mul_right
    exact hiA.add hiB
  have hiE : Integrable (fun x => χ x ^ 2 * ‖fderiv ℝ h x‖ ^ 2) :=
    ((hχ.continuous.pow 2).mul (hdc.norm.pow 2)).integrable_of_hasCompactSupport hc2.mul_right
  have hiB : Integrable (fun x => χ x * h x * (fderiv ℝ χ x 1 * fderiv ℝ h x 1 +
      fderiv ℝ χ x Complex.I * fderiv ℝ h x Complex.I)) :=
    ((hχ.continuous.mul hh.continuous).mul
      (((hχd 1).mul (hd 1)).add ((hχd Complex.I).mul (hd Complex.I)))).integrable_of_hasCompactSupport
      hχc.mul_right.mul_right
  have hsum := congrArg₂ (fun a b : ℝ => a + b)
    (logGreen_cutoff_direction hh hχ hχc 1)
    (logGreen_cutoff_direction hh hχ hχc Complex.I)
  rw [← integral_add (hiL 1) (hiL Complex.I)] at hsum
  rw [← neg_add, ← integral_add (hiR 1) (hiR Complex.I)] at hsum
  have heL : (fun x => χ x ^ 2 * h x * fderiv ℝ (fun y => fderiv ℝ h y 1) x 1 +
      χ x ^ 2 * h x * fderiv ℝ (fun y => fderiv ℝ h y Complex.I) x Complex.I) =
      (fun x => χ x ^ 2 * h x * Laplacian.laplacian h x) := by
    funext x
    rw [laplacian_eq_second_fderiv hh]
    dsimp only
    ring
  have heR : (fun x =>
      (χ x ^ 2 * (fderiv ℝ h x 1) ^ 2 + 2 * χ x * h x * fderiv ℝ χ x 1 * fderiv ℝ h x 1) +
      (χ x ^ 2 * (fderiv ℝ h x Complex.I) ^ 2 + 2 * χ x * h x * fderiv ℝ χ x Complex.I * fderiv ℝ h x Complex.I)) =
      (fun x => χ x ^ 2 * ‖fderiv ℝ h x‖ ^ 2 + 2 * (χ x * h x *
        (fderiv ℝ χ x 1 * fderiv ℝ h x 1 + fderiv ℝ χ x Complex.I * fderiv ℝ h x Complex.I))) := by
    funext x
    rw [planarFunctional_norm_sq]
    ring
  rw [heL, heR, integral_add hiE (hiB.const_mul 2), integral_const_mul] at hsum
  linarith

/-- The cutoff identity applied to the literal logarithmic potential and its
proved physical Poisson equation. Boundary passage is a separate obligation. -/
theorem smoothLogPotential_green_cutoff {η χ : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * ‖fderiv ℝ (smoothLogPotential η) x‖ ^ 2) =
      (2 * Real.pi) * (∫ x, χ x ^ 2 * smoothLogPotential η x * η x) -
      2 * (∫ x, χ x * smoothLogPotential η x *
        (fderiv ℝ χ x 1 * fderiv ℝ (smoothLogPotential η) x 1 +
          fderiv ℝ χ x Complex.I * fderiv ℝ (smoothLogPotential η) x Complex.I)) := by
  have h := logGreen_cutoff_identity (smoothLogPotential_contDiff (n := 2) hη hηc) hχ hχc
  rw [h]
  simp only [smoothLogPotential_laplacian hη hηc]
  congr 1
  rw [← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  ring

end RepulsiveCoulomb.PaperRoute
