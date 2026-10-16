import LeanResearch.RepulsiveCoulomb.PointWeightedSegment
import Mathlib.MeasureTheory.Measure.AEDisjoint

/-! The actual raw-weighted Hausdorff length measure and exact finite edge-length
accounting when distinct edges intersect only in finitely many points. -/
noncomputable section
open Set MeasureTheory AffineMap
open scoped BigOperators ENNReal Function
namespace RepulsiveCoulomb

def rawPointLengthMeasure {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Measure ℂ :=
  (Measure.euclideanHausdorffMeasure 1).withDensity (fun z => ENNReal.ofReal (rawPointWeight a y z))

theorem rawPointLengthMeasure_singleton {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (z : ℂ) : rawPointLengthMeasure a y {z} = 0 := by
  haveI : NullSingletonClass (Measure.hausdorffMeasure (1 : ℝ) : Measure ℂ) :=
    Measure.nullSingletonClass_hausdorff ℂ (by norm_num)
  have hzero : (Measure.euclideanHausdorffMeasure 1 : Measure ℂ) {z} = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    simp
  exact withDensity_absolutelyContinuous _ _ hzero

instance rawPointLengthMeasure_nullSingletonClass {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    NullSingletonClass (rawPointLengthMeasure a y) := ⟨rawPointLengthMeasure_singleton a y⟩

theorem rawPointLengthMeasure_segment {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z) :
    rawPointLengthMeasure a y ((lineMap x z) '' Icc (0 : ℝ) 1) =
      ENNReal.ofReal (rawPointSegmentLength a y x z) := by
  rw [rawPointLengthMeasure, withDensity_apply _
    (isCompact_Icc.image (contDiff_lineMap x z : ContDiff ℝ 1 (lineMap x z)).continuous).measurableSet]
  exact point_weighted_hausdorff_segment ha y hxz

theorem rawPointLengthMeasure_finite_edges {ι : Type*} [Fintype ι]
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (x z : ι → ℂ) (hnd : ∀ i, x i ≠ z i)
    (hfin : ∀ i j, i ≠ j →
      (((lineMap (x i) (z i)) '' Icc (0 : ℝ) 1) ∩
        ((lineMap (x j) (z j)) '' Icc (0 : ℝ) 1)).Finite) :
    rawPointLengthMeasure a y (⋃ i, (lineMap (x i) (z i)) '' Icc (0 : ℝ) 1) =
      ∑ i, ENNReal.ofReal (rawPointSegmentLength a y (x i) (z i)) := by
  have hd : Pairwise (AEDisjoint (rawPointLengthMeasure a y) on
      (fun i => (lineMap (x i) (z i)) '' Icc (0 : ℝ) 1)) := by
    intro i j hij
    exact (hfin i j hij).measure_zero (rawPointLengthMeasure a y)
  rw [measure_iUnion₀ hd (fun i =>
    ((isCompact_Icc.image (contDiff_lineMap (x i) (z i) :
      ContDiff ℝ 1 (lineMap (x i) (z i))).continuous).measurableSet).nullMeasurableSet)]
  simp only [tsum_fintype, rawPointLengthMeasure_segment ha y (hnd _)]

end RepulsiveCoulomb
