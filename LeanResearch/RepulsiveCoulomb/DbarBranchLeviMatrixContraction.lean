import LeanResearch.RepulsiveCoulomb.DbarBranchPotentialHessianPair
import LeanResearch.RepulsiveCoulomb.DbarBranchClassicalCR

/-! Exact conversion from a real bilinear Hessian to its Hermitian coordinate
contraction. The sign is fixed by the convention partial_j followed by dbar_i.
The actual Coulomb contraction then has coefficient beta/2. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def dbarRealHessianMatrix {N : ℕ} (B : CoulombConfig N →L[ℝ] CoulombConfig N →L[ℝ] ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  (((B (coulombCoordinateInjection N i 1) (coulombCoordinateInjection N j 1) +
      B (coulombCoordinateInjection N i Complex.I) (coulombCoordinateInjection N j Complex.I)) / 4 : ℝ) : ℂ) +
    Complex.I * (((B (coulombCoordinateInjection N i Complex.I) (coulombCoordinateInjection N j 1) -
      B (coulombCoordinateInjection N i 1) (coulombCoordinateInjection N j Complex.I)) / 4 : ℝ) : ℂ)

theorem dbarRealBilinear_coordinate_expand {N : ℕ}
    (B : CoulombConfig N →L[ℝ] CoulombConfig N →L[ℝ] ℝ) (i j : Fin N) (x y : ℂ) :
    B (coulombCoordinateInjection N i x) (coulombCoordinateInjection N j y) =
      x.re * y.re * B (coulombCoordinateInjection N i 1) (coulombCoordinateInjection N j 1) +
      x.re * y.im * B (coulombCoordinateInjection N i 1) (coulombCoordinateInjection N j Complex.I) +
      x.im * y.re * B (coulombCoordinateInjection N i Complex.I) (coulombCoordinateInjection N j 1) +
      x.im * y.im * B (coulombCoordinateInjection N i Complex.I) (coulombCoordinateInjection N j Complex.I) := by
  rw [coulombCoordinateInjection_real_decomposition i x, coulombCoordinateInjection_real_decomposition j y]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dbarRealBilinear_sum_coordinates {N : ℕ}
    (B : CoulombConfig N →L[ℝ] CoulombConfig N →L[ℝ] ℝ) (v w : CoulombConfig N) :
    B v w = ∑ i, ∑ j, B (coulombCoordinateInjection N i (v i)) (coulombCoordinateInjection N j (w j)) := by
  calc
    _ = B (∑ i, coulombCoordinateInjection N i (v i))
        (∑ j, coulombCoordinateInjection N j (w j)) := by
      rw [coulombCoordinateInjection_sum, coulombCoordinateInjection_sum]
    _ = _ := by
      simp only [map_sum, ContinuousLinearMap.sum_apply]
      exact Finset.sum_comm

theorem dbarRealHessianMatrix_entry_contraction {N : ℕ}
    (B : CoulombConfig N →L[ℝ] CoulombConfig N →L[ℝ] ℝ) (i j : Fin N) (x y : ℂ) :
    (conj x * dbarRealHessianMatrix B i j * y).re = (1 / 4 : ℝ) *
      (B (coulombCoordinateInjection N i x) (coulombCoordinateInjection N j y) +
        B (coulombCoordinateInjection N i (Complex.I * x)) (coulombCoordinateInjection N j (Complex.I * y))) := by
  rw [dbarRealBilinear_coordinate_expand B i j x y,
    dbarRealBilinear_coordinate_expand B i j (Complex.I * x) (Complex.I * y)]
  simp only [dbarRealHessianMatrix, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem dbarRealHessianMatrix_contraction {N : ℕ}
    (B : CoulombConfig N →L[ℝ] CoulombConfig N →L[ℝ] ℝ) (v : CoulombConfig N) :
    (∑ i, ∑ j, conj (v i) * dbarRealHessianMatrix B i j * v j).re =
      (1 / 4 : ℝ) * (B v v + B (Complex.I • v) (Complex.I • v)) := by
  rw [dbarRealBilinear_sum_coordinates B v v,
    dbarRealBilinear_sum_coordinates B (Complex.I • v) (Complex.I • v)]
  simp only [Complex.re_sum, dbarRealHessianMatrix_entry_contraction, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]

theorem coulombPotential_levi_matrix_contraction {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    (∑ i, ∑ j, conj (v i) *
      dbarRealHessianMatrix (fderiv ℝ (fderiv ℝ (coulombPotential β)) z) i j * v j).re =
        (β / 2) * ‖v‖ ^ 2 := by
  rw [dbarRealHessianMatrix_contraction]
  exact coulombPotential_hessian_levi_contraction β hz v

end RepulsiveCoulomb
