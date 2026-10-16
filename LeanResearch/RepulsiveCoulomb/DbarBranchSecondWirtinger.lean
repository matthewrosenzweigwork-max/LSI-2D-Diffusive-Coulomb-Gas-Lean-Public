module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWirtingerAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-! Actual second Wirtinger differentiation and commutation on C2 germs,
proved from the symmetric real Frechet Hessian. -/
noncomputable section
open InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombDbarCoordinate_hasFDerivAt {N : ℕ} {f : CoulombConfig N → ℂ}
    {z : CoulombConfig N} (hf : ContDiffAt ℝ 2 f z) (i : Fin N) :
    HasFDerivAt (fun x => coulombDbarCoordinate f x i)
      ((1 / 2 : ℂ) •
        ((fderiv ℝ (fderiv ℝ f) z).flip (coulombCoordinateInjection N i 1) +
          Complex.I • (fderiv ℝ (fderiv ℝ f) z).flip (coulombCoordinateInjection N i Complex.I))) z := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coulombCoordinateInjection N i 1) z)
  have hy := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coulombCoordinateInjection N i Complex.I) z)
  have h := (hx.add (hy.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have he : (fun x => coulombDbarCoordinate f x i) =
      fun x => (1 / 2 : ℂ) * (fderiv ℝ f x (coulombCoordinateInjection N i 1) +
        Complex.I * fderiv ℝ f x (coulombCoordinateInjection N i Complex.I)) := by
    funext x
    unfold coulombDbarCoordinate
    ring
  rw [he]
  simpa only [ContinuousLinearMap.comp_zero, zero_add, Pi.add_apply] using h

theorem coulombDCoordinate_hasFDerivAt {N : ℕ} {f : CoulombConfig N → ℂ}
    {z : CoulombConfig N} (hf : ContDiffAt ℝ 2 f z) (i : Fin N) :
    HasFDerivAt (fun x => coulombDCoordinate f x i)
      ((1 / 2 : ℂ) •
        ((fderiv ℝ (fderiv ℝ f) z).flip (coulombCoordinateInjection N i 1) -
          Complex.I • (fderiv ℝ (fderiv ℝ f) z).flip (coulombCoordinateInjection N i Complex.I))) z := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coulombCoordinateInjection N i 1) z)
  have hy := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (coulombCoordinateInjection N i Complex.I) z)
  have h := (hx.sub (hy.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have he : (fun x => coulombDCoordinate f x i) =
      fun x => (1 / 2 : ℂ) * (fderiv ℝ f x (coulombCoordinateInjection N i 1) -
        Complex.I * fderiv ℝ f x (coulombCoordinateInjection N i Complex.I)) := by
    funext x
    unfold coulombDCoordinate
    ring
  rw [he]
  simpa only [ContinuousLinearMap.comp_zero, zero_add, Pi.sub_apply] using h

theorem coulombDbar_D_commute {N : ℕ} {f : CoulombConfig N → ℂ}
    {z : CoulombConfig N} (hf : ContDiffAt ℝ 2 f z) (i j : Fin N) :
    coulombDbarCoordinate (fun x => coulombDCoordinate f x j) z i =
      coulombDCoordinate (fun x => coulombDbarCoordinate f x i) z j := by
  rw [coulombDbarCoordinate, coulombDCoordinate,
    (coulombDCoordinate_hasFDerivAt hf j).fderiv, (coulombDbarCoordinate_hasFDerivAt hf i).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  have hsym := hf.isSymmSndFDerivAt (by norm_num)
  rw [hsym.eq (coulombCoordinateInjection N j 1) (coulombCoordinateInjection N i 1),
    hsym.eq (coulombCoordinateInjection N j 1) (coulombCoordinateInjection N i Complex.I),
    hsym.eq (coulombCoordinateInjection N j Complex.I) (coulombCoordinateInjection N i 1),
    hsym.eq (coulombCoordinateInjection N j Complex.I) (coulombCoordinateInjection N i Complex.I)]
  ring

end RepulsiveCoulomb
