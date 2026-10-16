import LeanResearch.RepulsiveCoulomb.CoulombCenterGaussian
import LeanResearch.RepulsiveCoulomb.CoulombPermutationCore

/-! Exact physical-gradient identities in an all-particle orthonormal chart.
The real Euclidean metric, including the sum of the center and relative
energies, is used throughout. These statements contain no analytic estimate. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterRelativeInjection (n : ℕ) :
    CoulombConfig n →ₗᵢ[ℝ] CoulombConfig (n + 1) where
  toFun := coulombInsertZero 0
  map_add' r s := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coulombInsertZero_zero, PiLp.add_apply, add_zero]
    · rfl
  map_smul' a r := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coulombInsertZero_zero, PiLp.smul_apply, smul_zero, RingHom.id_apply]
    · rfl
  norm_map' r := by
    change ‖coulombInsertZero 0 r‖ = ‖r‖
    have h := coulombInsertZero_norm_sq (0 : ℂ) r
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
    nlinarith [norm_nonneg (coulombInsertZero 0 r), norm_nonneg r]

theorem coulombCenterRelativeInjection_apply (r : CoulombConfig n) :
    coulombCenterRelativeInjection n r = coulombInsertZero 0 r := rfl

theorem coulombCenter_relative_inner (z : CoulombConfig (n + 1))
    (v : CoulombConfig n) :
    inner ℝ z (coulombCenterRelativeInjection n v) = inner ℝ (coulombTail z) v := by
  simp only [coulombCenterRelativeInjection_apply, PiLp.inner_apply,
    Fin.sum_univ_succ, coulombInsertZero_zero, inner_zero_right, zero_add,
    coulombInsertZero_succ]
  rfl

theorem coulombInsertZero_hasFDerivAt_relative (c : ℂ) (r : CoulombConfig n) :
    HasFDerivAt (fun s : CoulombConfig n => coulombInsertZero c s)
      (coulombCenterRelativeInjection n).toContinuousLinearMap r := by
  have he : (fun s : CoulombConfig n => coulombInsertZero c s) =
      fun s => coulombInsertZero c (0 : CoulombConfig n) +
        coulombCenterRelativeInjection n s := by
    funext s
    exact coulombInsertZero_add_axes c s
  rw [he]
  exact (coulombCenterRelativeInjection n).toContinuousLinearMap.hasFDerivAt.const_add _

theorem coulombCenter_relative_slice_gradient {f : CoulombConfig (n + 1) → ℝ}
    (c : ℂ) (r : CoulombConfig n)
    (hf : DifferentiableAt ℝ f (coulombInsertZero c r)) :
    gradient (fun s => f (coulombInsertZero c s)) r =
      coulombTail (gradient f (coulombInsertZero c r)) := by
  have h := hf.hasFDerivAt.comp r (coulombInsertZero_hasFDerivAt_relative c r)
  apply (toDual ℝ (CoulombConfig n)).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ fun s => coulombInsertZero c s) r = _
  rw [h.fderiv]
  ext v
  change fderiv ℝ f (coulombInsertZero c r) (coulombCenterRelativeInjection n v) =
    inner ℝ (coulombTail (gradient f (coulombInsertZero c r))) v
  rw [← inner_gradient_left]
  exact coulombCenter_relative_inner _ v

/-- The entire rotated physical gradient transforms by the inverse transpose. -/
theorem coulombCenter_rotated_gradient (e : CoulombCenterRotation n)
    {f : CoulombConfig (n + 1) → ℝ} (x : CoulombConfig (n + 1))
    (hf : DifferentiableAt ℝ f (e.symm x)) :
    gradient (fun z => f (e.symm z)) x = e (gradient f (e.symm x)) :=
  gradient_comp_linearIsometryEquiv e.symm x hf

theorem coulombCenter_center_gradient (e : CoulombCenterRotation n)
    {f : CoulombConfig (n + 1) → ℝ} (c : ℂ) (r : CoulombConfig n)
    (hf : DifferentiableAt ℝ f (coulombCenterInsert e c r)) :
    gradient (fun w : ℂ => f (coulombCenterInsert e w r)) c =
      e (gradient f (coulombCenterInsert e c r)) 0 := by
  have hd : DifferentiableAt ℝ (fun z => f (e.symm z)) (coulombInsertZero c r) :=
    (show DifferentiableAt ℝ f (e.symm (coulombInsertZero c r)) from hf).comp
      (coulombInsertZero c r) e.symm.toContinuousLinearEquiv.differentiableAt
  have h := coulomb_first_slice_gradient r c hd
  rw [coulombCenter_rotated_gradient e _ hf] at h
  exact h

theorem coulombCenter_relative_gradient (e : CoulombCenterRotation n)
    {f : CoulombConfig (n + 1) → ℝ} (c : ℂ) (r : CoulombConfig n)
    (hf : DifferentiableAt ℝ f (coulombCenterInsert e c r)) :
    gradient (fun s : CoulombConfig n => f (coulombCenterInsert e c s)) r =
      coulombTail (e (gradient f (coulombCenterInsert e c r))) := by
  have hd : DifferentiableAt ℝ (fun z => f (e.symm z)) (coulombInsertZero c r) :=
    (show DifferentiableAt ℝ f (e.symm (coulombInsertZero c r)) from hf).comp
      (coulombInsertZero c r) e.symm.toContinuousLinearEquiv.differentiableAt
  have h := coulombCenter_relative_slice_gradient c r hd
  rw [coulombCenter_rotated_gradient e _ hf] at h
  exact h

/-- Unit physical energy splits with coefficient exactly one in both factors. -/
theorem coulombCenter_gradient_norm_sq (e : CoulombCenterRotation n)
    {f : CoulombConfig (n + 1) → ℝ} (c : ℂ) (r : CoulombConfig n)
    (hf : DifferentiableAt ℝ f (coulombCenterInsert e c r)) :
    ‖gradient f (coulombCenterInsert e c r)‖ ^ 2 =
      ‖gradient (fun w : ℂ => f (coulombCenterInsert e w r)) c‖ ^ 2 +
        ‖gradient (fun s : CoulombConfig n => f (coulombCenterInsert e c s)) r‖ ^ 2 := by
  rw [coulombCenter_center_gradient e c r hf, coulombCenter_relative_gradient e c r hf]
  have h := coulombInsertZero_norm_sq
    (e (gradient f (coulombCenterInsert e c r)) 0)
    (coulombTail (e (gradient f (coulombCenterInsert e c r))))
  rw [coulombInsertZero_head_tail, e.norm_map] at h
  exact h

end RepulsiveCoulomb
