import LeanResearch.RepulsiveCoulomb.CoulombPairRotation

/-! Exact center-frozen relative slice and its physical gradient. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombRelativeInsert {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    CoulombConfig (N + 2) :=
  coulombPairRotate N (coulombInsertZero c (coulombInsertZero u y))

theorem coulombRelativeInsert_zero {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeInsert c u y 0 = (Real.sqrt 2)⁻¹ • (c + u) := rfl

theorem coulombRelativeInsert_one {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeInsert c u y (Fin.succ 0) = (Real.sqrt 2)⁻¹ • (c - u) := rfl

theorem coulombRelativeInsert_succ_succ {N : ℕ} (c u : ℂ) (y : CoulombConfig N) (j : Fin N) :
    coulombRelativeInsert c u y j.succ.succ = y j := rfl

def coulombRelativeInjection (N : ℕ) : ℂ →L[ℝ] CoulombConfig (N + 2) :=
  (Real.sqrt 2)⁻¹ •
    (coulombCoordinateInjection (N + 2) 0 - coulombCoordinateInjection (N + 2) (Fin.succ 0))

theorem coulombRelativeInsert_affine {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeInsert c u y = coulombRelativeInjection N u + coulombRelativeInsert c 0 y := by
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp only [coulombRelativeInsert_zero, coulombRelativeInjection,
      smul_apply, sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      coulombCoordinateInjection_eq_single, PiLp.single_apply,
      ite_true, (Fin.succ_ne_zero (0 : Fin (N + 1))).symm, ite_false]
    module
  · simp only [coulombRelativeInsert_one, coulombRelativeInjection,
      smul_apply, sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      coulombCoordinateInjection_eq_single, PiLp.single_apply,
      ite_true, Fin.succ_ne_zero, ite_false]
    module
  · simp only [coulombRelativeInsert_succ_succ, coulombRelativeInjection,
      smul_apply, sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      coulombCoordinateInjection_eq_single, PiLp.single_apply,
      Fin.succ_ne_zero, Fin.succ_inj, ite_false, sub_self, smul_zero, zero_add]

theorem coulombRelativeInsert_contDiff {N : ℕ} (c : ℂ) (y : CoulombConfig N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => coulombRelativeInsert c u y) := by
  have he : (fun u => coulombRelativeInsert c u y) =
      fun u => coulombRelativeInjection N u + coulombRelativeInsert c 0 y :=
    funext (fun u => coulombRelativeInsert_affine c u y)
  rw [he]
  exact (coulombRelativeInjection N).contDiff.add contDiff_const

theorem coulombRelativeInsert_hasFDerivAt {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    HasFDerivAt (fun v => coulombRelativeInsert c v y) (coulombRelativeInjection N) u := by
  have he : (fun v => coulombRelativeInsert c v y) =
      fun v => coulombRelativeInjection N v + coulombRelativeInsert c 0 y :=
    funext (fun v => coulombRelativeInsert_affine c v y)
  rw [he]
  exact (coulombRelativeInjection N).hasFDerivAt.add_const _

theorem coulomb_inner_relative_injection {N : ℕ} (z : CoulombConfig (N + 2)) (w : ℂ) :
    inner ℝ z (coulombRelativeInjection N w) =
      inner ℝ ((Real.sqrt 2)⁻¹ • (z 0 - z (Fin.succ 0))) w := by
  simp only [coulombRelativeInjection, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, inner_smul_right, inner_sub_right,
    coulomb_inner_coordinate_injection, real_inner_smul_left, inner_sub_left]

theorem coulomb_relative_slice_gradient {N : ℕ} {f : CoulombConfig (N + 2) → ℝ}
    (c u : ℂ) (y : CoulombConfig N) (hf : DifferentiableAt ℝ f (coulombRelativeInsert c u y)) :
    gradient (fun v => f (coulombRelativeInsert c v y)) u =
      (Real.sqrt 2)⁻¹ • (gradient f (coulombRelativeInsert c u y) 0 -
        gradient f (coulombRelativeInsert c u y) (Fin.succ 0)) := by
  have h := hf.hasFDerivAt.comp u (coulombRelativeInsert_hasFDerivAt c u y)
  apply (toDual ℝ ℂ).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ fun v => coulombRelativeInsert c v y) u = _
  rw [h.fderiv]
  ext w
  change fderiv ℝ f (coulombRelativeInsert c u y) (coulombRelativeInjection N w) =
    inner ℝ ((Real.sqrt 2)⁻¹ • (gradient f (coulombRelativeInsert c u y) 0 -
      gradient f (coulombRelativeInsert c u y) (Fin.succ 0))) w
  rw [← inner_gradient_left]
  exact coulomb_inner_relative_injection _ w

end RepulsiveCoulomb

