module

public import LeanResearch.RepulsiveCoulomb.ComplexLinearJacobianBounds
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Planar cofactor and pointwise gradient transport

The real adjoint and the planar quarter-turn give a determinant-weighted
operator-norm bound for every real continuous-linear functional. The bound
requires neither invertibility nor a nonzero determinant.

The derivative corollaries use the actual derivatives of `F`, `g`, and `f`,
with the explicit composition identity `g ∘ F = f`. Quasiconformal distortion
and an upper Jacobian bound yield the pointwise square-root-weight estimate.
This file does not produce an inverse map, inverse differentiability, an
integrated gradient estimate, or a David–Semmes conclusion.
-/

noncomputable section

namespace RepulsiveCoulomb.PaperRoute

private theorem planar_apply_reIm (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = z.re • A 1 + z.im • A Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- The cofactor identity for an arbitrary real-linear map of the plane.
In particular, singular maps are included. -/
theorem planar_cofactor_identity (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A (Complex.I * A.adjoint z) =
      (A.toLinearMap.det : ℂ) * (Complex.I * z) := by
  have hre : (A.adjoint z).re = (A 1).re * z.re + (A 1).im * z.im := by
    have h := A.adjoint_inner_right (1 : ℂ) z
    simpa [Complex.inner, Complex.mul_re, mul_comm] using h
  have him : (A.adjoint z).im =
      (A Complex.I).re * z.re + (A Complex.I).im * z.im := by
    have h := A.adjoint_inner_right Complex.I z
    simpa [Complex.inner, Complex.mul_re, mul_comm] using h
  rw [planar_apply_reIm, complex_realLinear_det_formula]
  apply Complex.ext <;>
    simp only [ContinuousLinearMap.coe_coe, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, hre, him] <;> ring

/-- The actual determinant weights the full norm of a real functional, even
when the map is singular. No inverse or division by the determinant is used. -/
theorem abs_det_mul_norm_le_comp_norm_mul_norm
    (A : ℂ →L[ℝ] ℂ) (ℓ : ℂ →L[ℝ] ℝ) :
    |A.toLinearMap.det| * ‖ℓ‖ ≤ ‖ℓ.comp A‖ * ‖A‖ := by
  have hpoint (v : ℂ) :
      ‖(A.toLinearMap.det • ℓ) v‖ ≤ (‖ℓ.comp A‖ * ‖A‖) * ‖v‖ := by
    let q : ℂ := Complex.I * A.adjoint (-Complex.I * v)
    have hrotation : Complex.I * (-Complex.I * v) = v := by
      rw [← mul_assoc]
      norm_num
    have hAq : A q = A.toLinearMap.det • v := by
      dsimp [q]
      rw [planar_cofactor_identity, hrotation]
    have hq : ‖q‖ ≤ ‖A‖ * ‖v‖ := by
      have h := A.adjoint.le_opNorm (-Complex.I * v)
      simpa only [q, norm_mul, norm_neg, Complex.norm_I, one_mul,
        ContinuousLinearMap.adjoint.norm_map] using h
    calc
      ‖(A.toLinearMap.det • ℓ) v‖ = ‖(ℓ.comp A) q‖ := by
        rw [smul_apply, ContinuousLinearMap.comp_apply, hAq, map_smul]
      _ ≤ ‖ℓ.comp A‖ * ‖q‖ := (ℓ.comp A).le_opNorm q
      _ ≤ ‖ℓ.comp A‖ * (‖A‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      _ = (‖ℓ.comp A‖ * ‖A‖) * ‖v‖ := (mul_assoc _ _ _).symm
  have hop := (A.toLinearMap.det • ℓ).opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpoint
  simpa only [norm_smul, Real.norm_eq_abs] using hop

/-- For a nonnegative actual determinant, its absolute value can be removed. -/
theorem det_mul_norm_le_comp_norm_mul_norm
    (A : ℂ →L[ℝ] ℂ) (ℓ : ℂ →L[ℝ] ℝ) (hJ : 0 ≤ A.toLinearMap.det) :
    A.toLinearMap.det * ‖ℓ‖ ≤ ‖ℓ.comp A‖ * ‖A‖ := by
  simpa only [abs_of_nonneg hJ] using abs_det_mul_norm_le_comp_norm_mul_norm A ℓ

/-- A convenient interface for a supplied derivative-chain equality. -/
theorem det_mul_norm_le_norm_mul_norm_of_comp_eq
    (A : ℂ →L[ℝ] ℂ) (ℓ B : ℂ →L[ℝ] ℝ)
    (hJ : 0 ≤ A.toLinearMap.det) (hcomp : ℓ.comp A = B) :
    A.toLinearMap.det * ‖ℓ‖ ≤ ‖B‖ * ‖A‖ := by
  simpa only [hcomp] using det_mul_norm_le_comp_norm_mul_norm A ℓ hJ

/-- Outer distortion and an upper Jacobian bound control the norm of the
actual linear map. Zero weight is permitted. -/
theorem norm_le_sqrt_mul_sqrt_of_distortion (A : ℂ →L[ℝ] ℂ)
    {K C w : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hQC : ‖A‖ ^ 2 ≤ K * A.toLinearMap.det)
    (hJw : A.toLinearMap.det ≤ C * w) :
    ‖A‖ ≤ Real.sqrt (K * C) * Real.sqrt w := by
  have hsq : ‖A‖ ^ 2 ≤ (K * C) * w := by
    calc
      ‖A‖ ^ 2 ≤ K * A.toLinearMap.det := hQC
      _ ≤ K * (C * w) := mul_le_mul_of_nonneg_left hJw hK
      _ = (K * C) * w := (mul_assoc _ _ _).symm
  simpa only [Real.sqrt_mul (mul_nonneg hK hC)] using Real.le_sqrt_of_sq_le hsq

/-- The full two-step pointwise estimate, from an explicit chain relation,
nonnegative Jacobian, outer distortion, and upper Jacobian comparison.
It assumes no gradient-transport or inverse-regularity conclusion. -/
theorem det_mul_norm_gradient_chain_of_comp_eq
    (A : ℂ →L[ℝ] ℂ) (ℓ B : ℂ →L[ℝ] ℝ)
    {K C w : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hJ : 0 ≤ A.toLinearMap.det) (hcomp : ℓ.comp A = B)
    (hQC : ‖A‖ ^ 2 ≤ K * A.toLinearMap.det)
    (hJw : A.toLinearMap.det ≤ C * w) :
    A.toLinearMap.det * ‖ℓ‖ ≤ ‖B‖ * ‖A‖ ∧
      ‖B‖ * ‖A‖ ≤ Real.sqrt (K * C) * ‖B‖ * Real.sqrt w := by
  refine ⟨det_mul_norm_le_norm_mul_norm_of_comp_eq A ℓ B hJ hcomp, ?_⟩
  calc
    ‖B‖ * ‖A‖ ≤ ‖B‖ * (Real.sqrt (K * C) * Real.sqrt w) :=
      mul_le_mul_of_nonneg_left (norm_le_sqrt_mul_sqrt_of_distortion A hK hC hQC hJw)
        (norm_nonneg _)
    _ = Real.sqrt (K * C) * ‖B‖ * Real.sqrt w := by ring

/-- The genuine chain rule supplies the composition equality between the
actual Frechet derivatives. No inverse map or inverse derivative is assumed. -/
theorem fderiv_det_mul_norm_le_of_comp {F : ℂ → ℂ} {g f : ℂ → ℝ} {x : ℂ}
    (hF : DifferentiableAt ℝ F x) (hg : DifferentiableAt ℝ g (F x))
    (hcomp : g ∘ F = f) (hJ : 0 ≤ (fderiv ℝ F x).toLinearMap.det) :
    (fderiv ℝ F x).toLinearMap.det * ‖fderiv ℝ g (F x)‖ ≤
      ‖fderiv ℝ f x‖ * ‖fderiv ℝ F x‖ := by
  apply det_mul_norm_le_norm_mul_norm_of_comp_eq _ _ _ hJ
  rw [← fderiv_comp x hg hF, hcomp]

/-- Pointwise gradient transport with the actual derivatives and Jacobian.
The chain identity is obtained from differentiability and `g ∘ F = f`.
This statement does not assert that an inverse pullback is differentiable. -/
theorem fderiv_det_mul_norm_gradient_chain_of_comp
    {F : ℂ → ℂ} {g f : ℂ → ℝ} {x : ℂ} {K C : ℝ} {w : ℂ → ℝ}
    (hF : DifferentiableAt ℝ F x) (hg : DifferentiableAt ℝ g (F x))
    (hcomp : g ∘ F = f) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hJ : 0 ≤ (fderiv ℝ F x).toLinearMap.det)
    (hQC : ‖fderiv ℝ F x‖ ^ 2 ≤ K * (fderiv ℝ F x).toLinearMap.det)
    (hJw : (fderiv ℝ F x).toLinearMap.det ≤ C * w x) :
    (fderiv ℝ F x).toLinearMap.det * ‖fderiv ℝ g (F x)‖ ≤
        ‖fderiv ℝ f x‖ * ‖fderiv ℝ F x‖ ∧
      ‖fderiv ℝ f x‖ * ‖fderiv ℝ F x‖ ≤
        Real.sqrt (K * C) * ‖fderiv ℝ f x‖ * Real.sqrt (w x) := by
  apply det_mul_norm_gradient_chain_of_comp_eq _ _ _ hK hC hJ _ hQC hJw
  rw [← fderiv_comp x hg hF, hcomp]

end RepulsiveCoulomb.PaperRoute
