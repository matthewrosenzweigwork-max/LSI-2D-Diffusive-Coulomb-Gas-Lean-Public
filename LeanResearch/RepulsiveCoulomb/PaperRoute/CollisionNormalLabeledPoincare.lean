import LeanResearch.RepulsiveCoulomb.CoulombAllPairsSwap
import LeanResearch.RepulsiveCoulomb.CoulombCollisionNull
import LeanResearch.RepulsiveCoulomb.CoulombPairRotation
import LeanResearch.RepulsiveCoulomb.PaperRoute.CollisionLogLabeledPoincare

/-! Additive original-paper producer. The actual unit-normal pair chart and induced tangential
Lebesgue measure. The chart stays in the physical Euclidean configuration
space; the product measurable chart is not treated as an isometry. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb.PaperRoute

def paperPairSelection {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) : Equiv.Perm (Fin (N + 2)) :=
  Classical.choose (exists_coulomb_pair_permutation i j hij)

theorem paperPairSelection_spec {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) :
    paperPairSelection i j hij 0 = i ∧ paperPairSelection i j hij (Fin.succ 0) = j :=
  Classical.choose_spec (exists_coulomb_pair_permutation i j hij)

def paperPairNormalChart {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) :
    CoulombConfig (N + 2) ≃ₗᵢ[ℝ] CoulombConfig (N + 2) :=
  (coulombPermute (paperPairSelection i j hij)).trans
    ((coulombPairRotateEquiv N).trans (coulombPermute (Equiv.swap 0 (Fin.succ 0))))

theorem paperPairNormalChart_zero {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j)
    (z : CoulombConfig (N + 2)) :
    paperPairNormalChart i j hij z 0 = (Real.sqrt 2)⁻¹ • (z i - z j) := by
  obtain ⟨hi, hj⟩ := paperPairSelection_spec i j hij
  change coulombPairRotate N (coulombPermute (paperPairSelection i j hij) z)
    (Equiv.swap 0 (Fin.succ 0) 0) = _
  rw [Equiv.swap_apply_left, coulombPairRotate_one, coulombPermute_apply,
    coulombPermute_apply, hi, hj]

theorem paperPairNormalChart_measurePreserving {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j) :
    MeasurePreserving (paperPairNormalChart i j hij)
      (volume : Measure (CoulombConfig (N + 2))) volume :=
  (paperPairNormalChart i j hij).measurePreserving

/-- Insertion into a fixed normal slice is an isometry in the tangential variable. -/
theorem cylindrical_tangent_insert_isometry {N : ℕ} (u : ℂ) :
    Isometry (fun y : CoulombConfig N => coulombInsertZero u y) := by
  apply Isometry.of_dist_eq
  intro x y
  have he : coulombInsertZero u x - coulombInsertZero u y = coulombInsertZero 0 (x - y) := by
    ext k
    exact Fin.cases (by change u - u = 0; exact sub_self u) (fun _ => rfl) k
  simp only [dist_eq_norm, he]
  have hs := coulombInsertZero_norm_sq (0 : ℂ) (x - y)
  simp only [norm_zero, zero_pow two_ne_zero, zero_add] at hs
  nlinarith [norm_nonneg (coulombInsertZero (0 : ℂ) (x - y)), norm_nonneg (x - y)]

def paperPairNormalTrace {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j)
    (y : CoulombConfig (N + 1)) : CoulombConfig (N + 2) :=
  (paperPairNormalChart i j hij).symm (coulombInsertZero 0 y)

theorem paperPairNormalTrace_isometry {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) :
    Isometry (paperPairNormalTrace i j hij) :=
  (paperPairNormalChart i j hij).symm.isometry.comp (cylindrical_tangent_insert_isometry 0)

def paperPairNormalDirac {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) :
    Measure (CoulombConfig (N + 2)) := Measure.map (paperPairNormalTrace i j hij) volume

theorem paperPairNormalTrace_collision {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j)
    (y : CoulombConfig (N + 1)) :
    paperPairNormalTrace i j hij y i = paperPairNormalTrace i j hij y j := by
  have hz : paperPairNormalChart i j hij (paperPairNormalTrace i j hij y) 0 = 0 := by
    simp only [paperPairNormalTrace, LinearIsometryEquiv.apply_symm_apply, coulombInsertZero_zero]
  rw [paperPairNormalChart_zero] at hz
  have hs : (Real.sqrt (2 : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne'
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hs)

theorem paperPairNormalTrace_test_integrable {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun y : CoulombConfig (N + 1) => φ (paperPairNormalTrace i j hij y)) :=
  (hφ.comp (paperPairNormalTrace_isometry i j hij).continuous).integrable_of_hasCompactSupport
    (hφc.comp_isClosedEmbedding (paperPairNormalTrace_isometry i j hij).isClosedEmbedding)

theorem paperPairNormalDirac_test_integrable {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable φ (paperPairNormalDirac i j hij) := by
  exact ((paperPairNormalTrace_isometry i j hij).isClosedEmbedding.measurableEmbedding.integrable_map_iff).mpr
    (paperPairNormalTrace_test_integrable i j hij hφ hφc)

theorem paperPairNormalDirac_integral {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : Continuous φ) :
    (∫ z, φ z ∂paperPairNormalDirac i j hij) =
      ∫ y : CoulombConfig (N + 1), φ (paperPairNormalTrace i j hij y) := by
  unfold paperPairNormalDirac
  exact integral_map (paperPairNormalTrace_isometry i j hij).continuous.measurable.aemeasurable
    hφ.aestronglyMeasurable

/-- The log scaling is explicitly almost everywhere, excluding the actual
pair collision null hyperplane. It is not asserted at the log-zero representative. -/
theorem paper_pair_log_unit_normal_ae {N : ℕ}
    (i j : Fin (N + 2)) (hij : i ≠ j) :
    (fun z : CoulombConfig (N + 2) => Real.log ‖z i - z j‖) =ᵐ[volume]
      (fun z => Real.log (Real.sqrt 2) + Real.log ‖paperPairNormalChart i j hij z 0‖) := by
  have hpair : ∀ᵐ z : CoulombConfig (N + 2), z i ≠ z j := by
    rw [ae_iff]
    simpa only [not_not] using coulomb_pair_collision_volume_zero hij
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  filter_upwards [hpair] with z hz
  have hnormal : paperPairNormalChart i j hij z 0 ≠ 0 := by
    rw [paperPairNormalChart_zero]
    exact smul_ne_zero (inv_ne_zero hs.ne') (sub_ne_zero.mpr hz)
  have he : z i - z j = Real.sqrt 2 • (paperPairNormalChart i j hij z 0) := by
    rw [paperPairNormalChart_zero, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
    Real.log_mul hs.ne' (norm_ne_zero_iff.mpr hnormal)]

end RepulsiveCoulomb.PaperRoute
