import LeanResearch.RepulsiveCoulomb.CoulombSliceGeometry

/-! Actual orthonormal center/relative coordinate rotation. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombTail {N : ℕ} (z : CoulombConfig (N + 1)) : CoulombConfig N :=
  WithLp.toLp 2 (fun j => z j.succ)

theorem coulombInsertZero_head_tail {N : ℕ} (z : CoulombConfig (N + 1)) :
    coulombInsertZero (z 0) (coulombTail z) = z := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

def coulombPairRotate (N : ℕ) (z : CoulombConfig (N + 2)) : CoulombConfig (N + 2) :=
  coulombInsertZero ((Real.sqrt 2)⁻¹ • (z 0 + z (Fin.succ 0)))
    (coulombInsertZero ((Real.sqrt 2)⁻¹ • (z 0 - z (Fin.succ 0)))
      (coulombTail (coulombTail z)))

theorem coulombPairRotate_zero (N : ℕ) (z : CoulombConfig (N + 2)) :
    coulombPairRotate N z 0 = (Real.sqrt 2)⁻¹ • (z 0 + z (Fin.succ 0)) := rfl

theorem coulombPairRotate_one (N : ℕ) (z : CoulombConfig (N + 2)) :
    coulombPairRotate N z (Fin.succ 0) = (Real.sqrt 2)⁻¹ • (z 0 - z (Fin.succ 0)) := rfl

theorem coulombPairRotate_succ_succ (N : ℕ) (z : CoulombConfig (N + 2)) (j : Fin N) :
    coulombPairRotate N z j.succ.succ = z j.succ.succ := rfl

def coulombPairRotateLinear (N : ℕ) : CoulombConfig (N + 2) →ₗ[ℝ] CoulombConfig (N + 2) where
  toFun := coulombPairRotate N
  map_add' z v := by
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [coulombPairRotate_zero, PiLp.add_apply]
      module
    · simp only [coulombPairRotate_one, PiLp.add_apply]
      module
    · rfl
  map_smul' r z := by
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [coulombPairRotate_zero, PiLp.smul_apply, RingHom.id_apply]
      module
    · simp only [coulombPairRotate_one, PiLp.smul_apply, RingHom.id_apply]
      module
    · rfl

theorem coulombPairRotate_involutive (N : ℕ) :
    Function.Involutive (coulombPairRotate N) := by
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp
    nlinarith
  intro z
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp only [coulombPairRotate_zero, coulombPairRotate_one]
    calc
      _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2) • z 0 := by module
      _ = z 0 := by rw [hs, one_smul]
  · simp only [coulombPairRotate_zero, coulombPairRotate_one]
    calc
      _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2) • z (Fin.succ 0) := by module
      _ = z (Fin.succ 0) := by rw [hs, one_smul]
  · rfl

theorem coulombPairRotate_norm (N : ℕ) (z : CoulombConfig (N + 2)) :
    ‖coulombPairRotate N z‖ = ‖z‖ := by
  have hs : ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
  have hp : 0 ≤ (Real.sqrt 2)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg 2)
  have hz : ‖z‖ ^ 2 = ‖z 0‖ ^ 2 + (‖z (Fin.succ 0)‖ ^ 2 +
      ‖coulombTail (coulombTail z)‖ ^ 2) := by
    conv_lhs => rw [← coulombInsertZero_head_tail z, coulombInsertZero_norm_sq]
    rw [← coulombInsertZero_head_tail (coulombTail z), coulombInsertZero_norm_sq]
    rfl
  have hr := parallelogram_law_with_norm ℂ (z 0) (z (Fin.succ 0))
  have he : ‖coulombPairRotate N z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [coulombPairRotate, coulombInsertZero_norm_sq, coulombInsertZero_norm_sq,
      norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp, mul_pow, mul_pow, hs, hz]
    nlinarith
  nlinarith [norm_nonneg (coulombPairRotate N z), norm_nonneg z]

def coulombPairRotateEquiv (N : ℕ) :
    CoulombConfig (N + 2) ≃ₗᵢ[ℝ] CoulombConfig (N + 2) where
  toLinearEquiv :=
    { coulombPairRotateLinear N with
      invFun := coulombPairRotate N
      left_inv := coulombPairRotate_involutive N
      right_inv := coulombPairRotate_involutive N }
  norm_map' := coulombPairRotate_norm N

theorem coulombPairRotate_measurePreserving (N : ℕ) :
    MeasurePreserving (coulombPairRotate N) (volume : Measure (CoulombConfig (N + 2))) volume :=
  (coulombPairRotateEquiv N).measurePreserving

end RepulsiveCoulomb

