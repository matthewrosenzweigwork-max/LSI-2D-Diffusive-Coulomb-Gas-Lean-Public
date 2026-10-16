import LeanResearch.RepulsiveCoulomb.CoulombHelmertOrthonormal

/-! Literal Helmert coordinate formulas and the concrete, hypothesis-free
center axis used by the center-of-mass density and measure factorization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

theorem coulombHelmertRaw_sum_apply {N : ℕ} (k : Fin N) (z : CoulombConfig N) :
    (∑ j, (coulombHelmertRaw k j : ℂ) * z j) =
      (∑ j ∈ Finset.Iio k, z j) - (k.val : ℂ) * z k := by
  have hterm (j : Fin N) :
      (coulombHelmertRaw k j : ℂ) * z j =
        (if j < k then z j else 0) -
          (if j = k then (k.val : ℂ) * z j else 0) := by
    by_cases hjk : j < k <;> by_cases heq : j = k <;>
      simp [coulombHelmertRaw, hjk, heq, sub_mul]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hf : Finset.univ.filter (fun j : Fin N => j < k) = Finset.Iio k := by
    ext j
    simp
  rw [← Finset.sum_filter, hf]
  simp

/-- The center coordinate is exactly the normalized sum of all particles. -/
theorem coulombHelmertEquiv_zero (n : ℕ) (z : CoulombConfig (n + 1)) :
    coulombHelmertEquiv n z 0 =
      ((Real.sqrt (n + 1 : ℝ))⁻¹ : ℂ) * ∑ j, z j := by
  rw [coulombHelmertEquiv_apply, coulombHelmertRow_zero, PiLp.inner_apply]
  simp [coulombHelmertRealVector, RCLike.inner_apply',
    coulombHelmertCenterScale, ← Finset.mul_sum, ← Finset.sum_mul, mul_comm]

/-- `Iio k.succ` is precisely the first `k+1` particle indices.  This is the
relative-coordinate formula, including the manuscript's sign and row order. -/
theorem coulombHelmertEquiv_succ (n : ℕ) (z : CoulombConfig (n + 1)) (k : Fin n) :
    coulombHelmertEquiv n z k.succ =
      ((Real.sqrt (((k.val : ℝ) + 1) * ((k.val : ℝ) + 2)))⁻¹ : ℂ) *
        ((∑ j ∈ Finset.Iio k.succ, z j) - ((k.val : ℂ) + 1) * z k.succ) := by
  rw [coulombHelmertEquiv_apply, coulombHelmertRow_succ, PiLp.inner_apply]
  simp only [coulombHelmertRealVector, PiLp.toLp_apply, RCLike.inner_apply',
    Complex.conj_ofReal, Complex.ofReal_mul, map_mul, mul_assoc]
  rw [← Finset.mul_sum, coulombHelmertRaw_sum_apply]
  simp only [coulombHelmertScale, Fin.val_succ, Nat.cast_add, Nat.cast_one, Complex.ofReal_inv]
  congr 2 <;> ring

/-- The complex unitary transform regarded as an isometry of the physical
real configuration space. -/
def coulombHelmertRotation (n : ℕ) : CoulombCenterRotation n where
  toLinearEquiv := (coulombHelmertEquiv n).toLinearEquiv.restrictScalars ℝ
  norm_map' := (coulombHelmertEquiv n).norm_map

theorem coulombHelmertRotation_apply (n : ℕ) (z : CoulombConfig (n + 1)) :
    coulombHelmertRotation n z = coulombHelmertEquiv n z := rfl

theorem coulombHelmertRotation_symm_apply (n : ℕ) (z : CoulombConfig (n + 1)) :
    (coulombHelmertRotation n).symm z = (coulombHelmertEquiv n).symm z := rfl

private theorem coulombHelmert_insert_axis (n : ℕ) (c : ℂ) :
    coulombInsertZero c (0 : CoulombConfig n) =
      c • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℂ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coulombInsertZero_zero]
  · simp [coulombInsertZero_succ]

theorem coulombHelmertEquiv_symm_axis (n : ℕ) (c : ℂ) :
    (coulombHelmertEquiv n).symm (coulombInsertZero c (0 : CoulombConfig n)) =
      c • coulombHelmertRow n 0 := by
  rw [coulombHelmert_insert_axis, map_smul]
  change c • (coulombHelmertBasis n).repr.symm
    (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℂ)) = _
  rw [OrthonormalBasis.repr_symm_single, coulombHelmertBasis_apply]

/-- The inverse center axis is the diagonal, with its exact normalization. -/
theorem coulombHelmertEquiv_symm_axis_apply (n : ℕ) (c : ℂ) (i : Fin (n + 1)) :
    (coulombHelmertEquiv n).symm (coulombInsertZero c (0 : CoulombConfig n)) i =
      ((Real.sqrt (n + 1 : ℝ))⁻¹ : ℂ) * c := by
  rw [coulombHelmertEquiv_symm_axis, coulombHelmertRow_zero]
  simp [coulombHelmertRealVector, coulombHelmertCenterScale, mul_comm]

theorem coulombHelmertRotation_axis (n : ℕ) :
    CoulombCenterAxis (coulombHelmertRotation n) := by
  intro c i j
  change (coulombHelmertEquiv n).symm _ i = (coulombHelmertEquiv n).symm _ j
  rw [coulombHelmertEquiv_symm_axis_apply, coulombHelmertEquiv_symm_axis_apply]

/-- Every inverse particle difference is independent of the center coordinate. -/
theorem coulombHelmertEquiv_symm_difference (n : ℕ) (c : ℂ)
    (r : CoulombConfig n) (i j : Fin (n + 1)) :
    (coulombHelmertEquiv n).symm (coulombInsertZero c r) i -
        (coulombHelmertEquiv n).symm (coulombInsertZero c r) j =
      (coulombHelmertEquiv n).symm (coulombInsertZero 0 r) i -
        (coulombHelmertEquiv n).symm (coulombInsertZero 0 r) j :=
  coulombCenterInsert_difference (coulombHelmertRotation n)
    (coulombHelmertRotation_axis n) c r i j

theorem coulombHelmertEquiv_inner (n : ℕ) (z w : CoulombConfig (n + 1)) :
    inner ℂ (coulombHelmertEquiv n z) (coulombHelmertEquiv n w) = inner ℂ z w :=
  (coulombHelmertEquiv n).inner_map_map z w

theorem coulombHelmertEquiv_norm (n : ℕ) (z : CoulombConfig (n + 1)) :
    ‖coulombHelmertEquiv n z‖ = ‖z‖ := (coulombHelmertEquiv n).norm_map z

theorem coulombHelmertEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (coulombHelmertEquiv n)
      (volume : Measure (CoulombConfig (n + 1))) volume :=
  (coulombHelmertRotation n).measurePreserving

theorem coulombHelmertEquiv_symm_norm_sq (n : ℕ) (c : ℂ) (r : CoulombConfig n) :
    ‖(coulombHelmertEquiv n).symm (coulombInsertZero c r)‖ ^ 2 =
      ‖c‖ ^ 2 + ‖r‖ ^ 2 := by
  rw [(coulombHelmertEquiv n).symm.norm_map, coulombInsertZero_norm_sq]

theorem coulombHelmertEquiv_norm_decomposition (n : ℕ) (z : CoulombConfig (n + 1)) :
    ‖z‖ ^ 2 = ‖coulombHelmertEquiv n z 0‖ ^ 2 +
      ‖coulombTail (coulombHelmertEquiv n z)‖ ^ 2 := by
  have h := coulombInsertZero_norm_sq (coulombHelmertEquiv n z 0)
    (coulombTail (coulombHelmertEquiv n z))
  rw [coulombInsertZero_head_tail, coulombHelmertEquiv_norm] at h
  exact h

end RepulsiveCoulomb
