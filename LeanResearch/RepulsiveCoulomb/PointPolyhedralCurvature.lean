module

public import LeanResearch.RepulsiveCoulomb.PointClassicalConeDisk
public import Mathlib.MeasureTheory.VectorMeasure.Order

@[expose] public section

/-! Finite atomic polyhedral curvature, read from the now-proved classical cone
angles. This is cone-angle curvature; no unproved distributional Laplacian
identity or global uniformization theorem is asserted. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem coalescedPointExponent_eq_zero_of_not_mem {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ positivePointLocations a y) :
    coalescedPointExponent a y p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hj, hyp⟩ := Finset.mem_filter.mp hj
  exact False.elim (hp ((mem_positivePointLocations a y p).mpr
    ⟨j, (mem_positivePointIndices a j).mp hj, hyp⟩))

theorem pointConeAngle_flat_iff {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    pointConeAngle a y p = 2 * Real.pi ↔ p ∉ positivePointLocations a y := by
  constructor
  · intro h hp
    rw [pointConeAngle_eq] at h
    have hb := coalescedPointExponent_pos a y hp
    nlinarith [Real.pi_pos]
  · intro hp
    rw [pointConeAngle_eq, coalescedPointExponent_eq_zero_of_not_mem a y hp, mul_zero, add_zero]

theorem sum_pointConeAngle_excess {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∑ p ∈ positivePointLocations a y, (pointConeAngle a y p - 2 * Real.pi) = Real.pi * ∑ j, a j := by
  simp_rw [pointConeAngle_eq, add_sub_cancel_left]
  rw [← Finset.mul_sum, sum_coalescedPointExponent ha y]

def pointConeNegativeCurvature {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Measure ℂ :=
  ∑ p ∈ positivePointLocations a y,
    ENNReal.ofReal (Real.pi * coalescedPointExponent a y p) • Measure.dirac p

theorem pointConeNegativeCurvature_univ {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    pointConeNegativeCurvature a y univ =
      ENNReal.ofReal (∑ p ∈ positivePointLocations a y, Real.pi * coalescedPointExponent a y p) := by
  rw [pointConeNegativeCurvature, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg (fun p _ ↦
    mul_nonneg Real.pi_pos.le (coalescedPointExponent_nonneg a y p))).symm

instance pointConeNegativeCurvature_finite {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    IsFiniteMeasure (pointConeNegativeCurvature a y) :=
  ⟨by rw [pointConeNegativeCurvature_univ]; exact ENNReal.ofReal_lt_top⟩

theorem pointConeNegativeCurvature_total {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointConeNegativeCurvature a y univ = ENNReal.ofReal (Real.pi * ∑ j, a j) := by
  rw [pointConeNegativeCurvature_univ, ← Finset.mul_sum, sum_coalescedPointExponent ha y]

theorem pointConeNegativeCurvature_singleton {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    pointConeNegativeCurvature a y {p} = ENNReal.ofReal (Real.pi * coalescedPointExponent a y p) := by
  classical
  rw [pointConeNegativeCurvature, Measure.finsetSum_apply]
  calc
    _ = (ENNReal.ofReal (Real.pi * coalescedPointExponent a y p) • Measure.dirac p) {p} := by
      apply Finset.sum_eq_single p
      · intro q _ hqp
        rw [Measure.smul_apply, Measure.dirac_apply' q (measurableSet_singleton p),
          Set.indicator_of_notMem (show q ∉ ({p} : Set ℂ) by simpa using hqp)]
        simp
      · intro hp
        rw [coalescedPointExponent_eq_zero_of_not_mem a y hp]
        simp
    _ = _ := by simp

def pointPolyhedralCurvature {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : SignedMeasure ℂ :=
  -(pointConeNegativeCurvature a y).toSignedMeasure

theorem pointPolyhedralCurvature_nonpos {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    pointPolyhedralCurvature a y ≤ 0 := neg_nonpos.mpr (Measure.zero_le_toSignedMeasure _)

theorem pointPolyhedralCurvature_singleton {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    pointPolyhedralCurvature a y {p} = 2 * Real.pi - pointConeAngle a y p := by
  simp only [pointPolyhedralCurvature, neg_apply, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton p),
    measureReal_def, pointConeNegativeCurvature_singleton,
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (coalescedPointExponent_nonneg a y p)), pointConeAngle_eq]
  ring

theorem pointPolyhedralCurvature_total {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointPolyhedralCurvature a y univ = -Real.pi * ∑ j, a j := by
  simp only [pointPolyhedralCurvature, neg_apply, Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    measureReal_def, pointConeNegativeCurvature_total ha y,
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (Finset.sum_nonneg (fun j _ ↦ ha j)))]
  ring

end RepulsiveCoulomb
