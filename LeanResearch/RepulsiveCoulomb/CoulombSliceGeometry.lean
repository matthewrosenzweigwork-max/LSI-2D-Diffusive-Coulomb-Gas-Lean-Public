module

public import LeanResearch.RepulsiveCoulomb.CoulombOneSiteKernel
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! Isometric coordinate insertion and the exact real physical slice gradient. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombCoordinateInjection (N : ℕ) (i : Fin N) : ℂ →L[ℝ] CoulombConfig N :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin N => ℂ) i)

theorem coulombCoordinateInjection_eq_single (N : ℕ) (i : Fin N) (w : ℂ) :
    coulombCoordinateInjection N i w = EuclideanSpace.single i w := rfl

theorem coulombCoordinateInjection_norm (N : ℕ) (i : Fin N) (w : ℂ) :
    ‖coulombCoordinateInjection N i w‖ = ‖w‖ := by
  rw [coulombCoordinateInjection_eq_single]
  exact PiLp.norm_single 2 (fun _ : Fin N => ℂ) i w

theorem coulombInsertZero_affine {N : ℕ} (w : ℂ) (y : CoulombConfig N) :
    coulombInsertZero w y = coulombCoordinateInjection (N + 1) 0 w + coulombInsertZero 0 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coulombCoordinateInjection_eq_single, coulombInsertZero_zero]
  · simp [coulombCoordinateInjection_eq_single, coulombInsertZero_succ]

theorem coulombInsertZero_contDiff {N : ℕ} (y : CoulombConfig N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => coulombInsertZero w y) := by
  have he : (fun w : ℂ => coulombInsertZero w y) =
      fun w => coulombCoordinateInjection (N + 1) 0 w + coulombInsertZero 0 y :=
    funext (fun w => coulombInsertZero_affine w y)
  rw [he]
  exact (coulombCoordinateInjection (N + 1) 0).contDiff.add contDiff_const

theorem coulombInsertZero_hasFDerivAt {N : ℕ} (y : CoulombConfig N) (w : ℂ) :
    HasFDerivAt (fun z : ℂ => coulombInsertZero z y) (coulombCoordinateInjection (N + 1) 0) w := by
  have he : (fun z : ℂ => coulombInsertZero z y) =
      fun z => coulombCoordinateInjection (N + 1) 0 z + coulombInsertZero 0 y :=
    funext (fun z => coulombInsertZero_affine z y)
  rw [he]
  exact (coulombCoordinateInjection (N + 1) 0).hasFDerivAt.add_const _

theorem coulombInsertZero_isometry {N : ℕ} (y : CoulombConfig N) :
    Isometry (fun w : ℂ => coulombInsertZero w y) := by
  apply Isometry.of_dist_eq
  intro w v
  simp only [dist_eq_norm]
  have he : coulombInsertZero w y - coulombInsertZero v y =
      coulombCoordinateInjection (N + 1) 0 (w - v) := by
    rw [coulombInsertZero_affine w y, coulombInsertZero_affine v y, map_sub]
    abel
  rw [he, coulombCoordinateInjection_norm]

theorem coulomb_inner_coordinate_injection {N : ℕ} (i : Fin N) (z : CoulombConfig N) (w : ℂ) :
    inner ℝ z (coulombCoordinateInjection N i w) = inner ℝ (z i) w := by
  rw [coulombCoordinateInjection_eq_single]
  simp [PiLp.inner_apply, apply_ite, Complex.mul_re]

theorem coulomb_first_slice_gradient {N : ℕ} {f : CoulombConfig (N + 1) → ℝ}
    (y : CoulombConfig N) (w : ℂ) (hf : DifferentiableAt ℝ f (coulombInsertZero w y)) :
    gradient (fun z => f (coulombInsertZero z y)) w = gradient f (coulombInsertZero w y) 0 := by
  have h := hf.hasFDerivAt.comp w (coulombInsertZero_hasFDerivAt y w)
  apply (toDual ℝ ℂ).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ fun z => coulombInsertZero z y) w = _
  rw [h.fderiv]
  ext v
  change fderiv ℝ f (coulombInsertZero w y) (coulombCoordinateInjection (N + 1) 0 v) =
    inner ℝ (gradient f (coulombInsertZero w y) 0) v
  rw [← inner_gradient_left]
  exact coulomb_inner_coordinate_injection 0 _ v

end RepulsiveCoulomb

