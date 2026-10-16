import LeanResearch.RepulsiveCoulomb.CoulombPotentialLaplacian

/-! The actual real Hessian contracted along a complex line. This uses the
checked local affine pullback and exact Coulomb Levi quadratic for every vector,
not an assumed coordinate curvature matrix. -/
noncomputable section
open Set InnerProductSpace
namespace RepulsiveCoulomb

def coulombComplexLineMap {N : ℕ} (v : CoulombConfig N) : ℂ →L[ℝ] CoulombConfig N :=
  (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ

theorem coulombComplexLineMap_apply {N : ℕ} (v : CoulombConfig N) (t : ℂ) :
    coulombComplexLineMap v t = t • v := rfl

theorem coulombPotential_hessian_complex_pair {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    fderiv ℝ (fderiv ℝ (coulombPotential β)) z v v +
      fderiv ℝ (fderiv ℝ (coulombPotential β)) z (Complex.I • v) (Complex.I • v) =
        2 * β * ‖v‖ ^ 2 := by
  have h := coulombPotential_line_laplacian β hz v
  have he : (fun t : ℂ => coulombPotential β (z + t • v)) =
      fun t : ℂ => coulombPotential β (z + coulombComplexLineMap v t) := rfl
  rw [he, laplacian_eq_iteratedFDeriv_complexPlane] at h
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hs : ContDiffOn ℝ 2 (coulombPotential (N := N) β) (coulombDomain N) :=
    fun x hx => ((coulombPotential_contDiffAt β hx).of_le (by simp)).contDiffWithinAt
  rw [local_affine_hessian (coulombDomain N).isOpen hs hz (coulombComplexLineMap v) 1 1,
    local_affine_hessian (coulombDomain N).isOpen hs hz (coulombComplexLineMap v) Complex.I Complex.I] at h
  simpa only [coulombComplexLineMap_apply, one_smul] using h

theorem coulombPotential_hessian_levi_contraction {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    (1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ (coulombPotential β)) z v v +
      fderiv ℝ (fderiv ℝ (coulombPotential β)) z (Complex.I • v) (Complex.I • v)) =
        (β / 2) * ‖v‖ ^ 2 := by
  rw [coulombPotential_hessian_complex_pair β hz v]
  ring

end RepulsiveCoulomb
