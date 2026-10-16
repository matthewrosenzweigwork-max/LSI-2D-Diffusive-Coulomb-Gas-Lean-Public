module

public import LeanResearch.RepulsiveCoulomb.CoulombSliceGeometry
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

/-! Literal Wirtinger coordinate derivatives, with the original real-gradient convention. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def coulombDbarCoordinate {N : ℕ} (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (i : Fin N) : ℂ :=
  (fderiv ℝ f z (coulombCoordinateInjection N i 1) +
    Complex.I * fderiv ℝ f z (coulombCoordinateInjection N i Complex.I)) / 2

def coulombDbar {N : ℕ} (f : CoulombConfig N → ℂ) (z : CoulombConfig N) : CoulombConfig N :=
  WithLp.toLp 2 (fun i => coulombDbarCoordinate f z i)

theorem coulombDbar_apply {N : ℕ} (f : CoulombConfig N → ℂ) (z : CoulombConfig N) (i : Fin N) :
    coulombDbar f z i = coulombDbarCoordinate f z i := rfl

theorem coulombCoordinateInjection_complex_smul {N : ℕ} (i : Fin N) (a w : ℂ) :
    coulombCoordinateInjection N i (a * w) = a • coulombCoordinateInjection N i w := by
  ext j
  by_cases h : j = i <;> simp [coulombCoordinateInjection_eq_single, EuclideanSpace.single,
    PiLp.single_apply, h]

theorem coulomb_real_axis_derivative {N : ℕ} (f : CoulombConfig N → ℝ) (z : CoulombConfig N)
    (i : Fin N) : fderiv ℝ f z (coulombCoordinateInjection N i 1) = (gradient f z i).re := by
  rw [← inner_gradient_left, coulomb_inner_coordinate_injection]
  simp [Complex.inner]

theorem coulomb_imag_axis_derivative {N : ℕ} (f : CoulombConfig N → ℝ) (z : CoulombConfig N)
    (i : Fin N) : fderiv ℝ f z (coulombCoordinateInjection N i Complex.I) = (gradient f z i).im := by
  rw [← inner_gradient_left, coulomb_inner_coordinate_injection]
  simp [Complex.inner, Complex.mul_re]

theorem coulombDbarCoordinate_real {N : ℕ} {f : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) (i : Fin N) :
    coulombDbarCoordinate (fun x => (f x : ℂ)) z i = gradient f z i / 2 := by
  have hd : fderiv ℝ (fun x => (f x : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ f z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  rw [coulombDbarCoordinate, hd]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    coulomb_real_axis_derivative, coulomb_imag_axis_derivative]
  congr 1
  simpa only [mul_comm] using Complex.re_add_im (gradient f z i)

theorem coulombDbar_real {N : ℕ} {f : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) :
    coulombDbar (fun x => (f x : ℂ)) z = (1 / 2 : ℂ) • gradient f z := by
  ext i
  rw [coulombDbar_apply, coulombDbarCoordinate_real hf]
  simp [div_eq_mul_inv, mul_comm]

theorem coulombDbar_real_norm_sq {N : ℕ} {f : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) :
    ‖coulombDbar (fun x => (f x : ℂ)) z‖ ^ 2 = (1 / 4 : ℝ) * ‖gradient f z‖ ^ 2 := by
  rw [coulombDbar_real hf, norm_smul, mul_pow]
  norm_num

theorem coulombDbar_real_sum_sq {N : ℕ} {f : CoulombConfig N → ℝ} {z : CoulombConfig N}
    (hf : DifferentiableAt ℝ f z) :
    (∑ i, ‖coulombDbarCoordinate (fun x => (f x : ℂ)) z i‖ ^ 2) =
      (1 / 4 : ℝ) * ‖gradient f z‖ ^ 2 := by
  rw [← coulombDbar_real_norm_sq hf, EuclideanSpace.norm_sq_eq]
  rfl

theorem coulombDbarCoordinate_of_complex_differentiable {N : ℕ}
    {f : CoulombConfig N → ℂ} {z : CoulombConfig N} (hf : DifferentiableAt ℂ f z) (i : Fin N) :
    coulombDbarCoordinate f z i = 0 := by
  rw [coulombDbarCoordinate, hf.fderiv_restrictScalars ℝ]
  have he : coulombCoordinateInjection N i Complex.I =
      Complex.I • coulombCoordinateInjection N i 1 := by
    simpa using coulombCoordinateInjection_complex_smul i Complex.I 1
  simp only [ContinuousLinearMap.coe_restrictScalars', he, map_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem coulombDbar_of_complex_differentiable {N : ℕ}
    {f : CoulombConfig N → ℂ} {z : CoulombConfig N} (hf : DifferentiableAt ℂ f z) :
    coulombDbar f z = 0 := by
  ext i
  exact coulombDbarCoordinate_of_complex_differentiable hf i

end RepulsiveCoulomb
