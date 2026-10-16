import LeanResearch.RepulsiveCoulomb.LocalAffineHessian
import LeanResearch.RepulsiveCoulomb.CoulombWirtinger

/-! Full real Laplacian of the actual particle potential, off all collisions. -/
noncomputable section
open Set InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

theorem coulombPotential_coordinate_trace {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (i : Fin N) :
    fderiv ℝ (fderiv ℝ (coulombPotential β)) z
      (coulombCoordinateInjection N i 1) (coulombCoordinateInjection N i 1) +
    fderiv ℝ (fderiv ℝ (coulombPotential β)) z
      (coulombCoordinateInjection N i Complex.I) (coulombCoordinateInjection N i Complex.I) = 2 * β := by
  have h := coulombPotential_line_laplacian β hz (coulombCoordinateInjection N i 1)
  have he : (fun t : ℂ => coulombPotential β (z + t • coulombCoordinateInjection N i 1)) =
      (fun t : ℂ => coulombPotential β (z + coulombCoordinateInjection N i t)) := by
    funext t
    congr 1
    exact congrArg (fun v : CoulombConfig N => z + v)
      (by simpa only [mul_one] using (coulombCoordinateInjection_complex_smul i t 1).symm)
  rw [he, laplacian_eq_iteratedFDeriv_complexPlane] at h
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hs : ContDiffOn ℝ 2 (coulombPotential (N := N) β) (coulombDomain N) := by
    intro x hx
    exact ((coulombPotential_contDiffAt (N := N) β hx).of_le (by simp)).contDiffWithinAt
  rw [local_affine_hessian (coulombDomain N).isOpen hs hz (coulombCoordinateInjection N i) 1 1,
    local_affine_hessian (coulombDomain N).isOpen hs hz (coulombCoordinateInjection N i) Complex.I Complex.I,
    coulombCoordinateInjection_norm, norm_one, one_pow, mul_one] at h
  exact h

theorem coulombPotential_laplacian {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    Laplacian.laplacian (coulombPotential β) z = 2 * (N : ℝ) * β := by
  let b := Pi.orthonormalBasis (fun _ : Fin N => Complex.orthonormalBasisOneI)
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (coulombPotential β) b]
  simp only [b, Fintype.sum_sigma, Fin.sum_univ_two, Pi.orthonormalBasis_apply,
    Complex.coe_orthonormalBasisOneI, iteratedFDeriv_two_apply]
  change (∑ i : Fin N,
    (fderiv ℝ (fderiv ℝ (coulombPotential β)) z
      (coulombCoordinateInjection N i 1) (coulombCoordinateInjection N i 1) +
    fderiv ℝ (fderiv ℝ (coulombPotential β)) z
      (coulombCoordinateInjection N i Complex.I) (coulombCoordinateInjection N i Complex.I))) = _
  simp_rw [coulombPotential_coordinate_trace β hz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end RepulsiveCoulomb
