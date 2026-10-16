module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeSlice

@[expose] public section

noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombRelativeInsert_norm_sq {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    ‖coulombRelativeInsert c u y‖ ^ 2 = ‖c‖ ^ 2 + (‖u‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [coulombRelativeInsert, coulombPairRotate_norm, coulombInsertZero_norm_sq,
    coulombInsertZero_norm_sq]

theorem coulombRelativeInsert_zero_all (N : ℕ) :
    coulombRelativeInsert 0 0 (0 : CoulombConfig N) = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp only [coulombRelativeInsert_zero, add_zero, smul_zero, PiLp.zero_apply]
  · simp only [coulombRelativeInsert_one, sub_zero, smul_zero, PiLp.zero_apply]
  · rfl

theorem coulombRelativeInjection_norm (N : ℕ) (u : ℂ) :
    ‖coulombRelativeInjection N u‖ = ‖u‖ := by
  have he := coulombRelativeInsert_affine (0 : ℂ) u (0 : CoulombConfig N)
  rw [coulombRelativeInsert_zero_all, add_zero] at he
  have hn := coulombRelativeInsert_norm_sq (0 : ℂ) u (0 : CoulombConfig N)
  rw [he] at hn
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, add_zero] at hn
  nlinarith [norm_nonneg (coulombRelativeInjection N u), norm_nonneg u]

theorem coulombRelativeInsert_isometry {N : ℕ} (c : ℂ) (y : CoulombConfig N) :
    Isometry (fun u => coulombRelativeInsert c u y) := by
  apply Isometry.of_dist_eq
  intro u v
  simp only [dist_eq_norm]
  have he : coulombRelativeInsert c u y - coulombRelativeInsert c v y =
      coulombRelativeInjection N (u - v) := by
    rw [coulombRelativeInsert_affine c u y, coulombRelativeInsert_affine c v y, map_sub]
    abel
  rw [he, coulombRelativeInjection_norm]

def coulombRelativeCoordinates (N : ℕ) :
    CoulombConfig (N + 2) ≃ᵐ ℂ × (ℂ × CoulombConfig N) :=
  (coulombPairRotateEquiv N).toMeasurableEquiv.trans
    ((coulombSplitZero (N + 1)).trans
      ((MeasurableEquiv.refl ℂ).prodCongr (coulombSplitZero N)))

theorem coulombRelativeCoordinates_measurePreserving (N : ℕ) :
    MeasurePreserving (coulombRelativeCoordinates N)
      (volume : Measure (CoulombConfig (N + 2))) volume := by
  exact (((MeasurePreserving.id (volume : Measure ℂ)).prod
    (coulombSplitZero_measurePreserving N)).comp
      (coulombSplitZero_measurePreserving (N + 1))).comp
        (coulombPairRotate_measurePreserving N)

theorem coulombRelativeCoordinates_insert {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeCoordinates N (coulombRelativeInsert c u y) = (c, (u, y)) := by
  change ((coulombSplitZero (N + 1)
    (coulombPairRotate N (coulombPairRotate N (coulombInsertZero c (coulombInsertZero u y))))).1,
    coulombSplitZero N ((coulombSplitZero (N + 1)
    (coulombPairRotate N (coulombPairRotate N (coulombInsertZero c (coulombInsertZero u y))))).2)) = _
  rw [coulombPairRotate_involutive N, coulombSplitZero_insert, coulombSplitZero_insert]

theorem coulombRelativeCoordinates_symm_apply {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    (coulombRelativeCoordinates N).symm (c, (u, y)) = coulombRelativeInsert c u y := by
  apply (coulombRelativeCoordinates N).injective
  rw [MeasurableEquiv.apply_symm_apply, coulombRelativeCoordinates_insert]

end RepulsiveCoulomb

