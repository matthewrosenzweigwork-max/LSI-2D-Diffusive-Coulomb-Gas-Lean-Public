import LeanResearch.RepulsiveCoulomb.ComplexLineLaplacian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! A genuine planar norm-square Laplacian identity, including the derivative-square terms. -/
noncomputable section
open InnerProductSpace Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem secondFDeriv_norm_sq_diag {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℂ → F} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => ‖f y‖ ^ 2)) x v v =
      2 * (inner ℝ (f x) (fderiv ℝ (fderiv ℝ f) x v v) + ‖fderiv ℝ f x v‖ ^ 2) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := hdd.clm_apply (differentiableAt_const v)
  have hg : ContDiffAt ℝ 2 (fun y => ‖f y‖ ^ 2) x :=
    (contDiff_norm_sq ℝ).contDiffAt.comp x hf
  have hgd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => fderiv ℝ (fun z => ‖f z‖ ^ 2) y v) =ᶠ[𝓝 x]
      (fun y => 2 * inner ℝ (f y) (fderiv ℝ f y v)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    rw [(hy.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp [two_smul, two_mul]
  have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) he.fderiv_eq
  rw [fderiv_clm_apply hgd (differentiableAt_const v),
    fderiv_const_mul (hfd.inner ℝ hfv) 2] at hh
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hh
  rw [fderiv_inner_apply ℝ hfd hfv v,
    fderiv_clm_apply hdd (differentiableAt_const v)] at hh
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, real_inner_self_eq_norm_sq] using hh

theorem planar_laplacian_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℂ → F} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x =
      2 * inner ℝ (f x) (Laplacian.laplacian f x) +
        2 * ‖fderiv ℝ f x 1‖ ^ 2 + 2 * ‖fderiv ℝ f x Complex.I‖ ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    secondFDeriv_norm_sq_diag hf, inner_add_right]
  ring

theorem harmonic_norm_sq_laplacian_nonneg {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℂ → F} {x : ℂ} (hf : HarmonicAt f x) :
    0 ≤ Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x := by
  rw [planar_laplacian_norm_sq hf.1, hf.2.self_of_nhds]
  simp only [Pi.zero_apply, inner_zero_right, mul_zero, zero_add]
  positivity

end RepulsiveCoulomb
