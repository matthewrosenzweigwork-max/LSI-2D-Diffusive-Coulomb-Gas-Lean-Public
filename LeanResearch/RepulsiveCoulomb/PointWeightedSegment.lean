module

public import LeanResearch.RepulsiveCoulomb.WeightedArcLength
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.AffineMap

@[expose] public section

/-! Literal weighted length of straight segments, including zero-length segments,
and its exact relation to normalized Hausdorff length for nondegenerate edges. -/
noncomputable section
open Set MeasureTheory AffineMap
open scoped ENNReal
namespace RepulsiveCoulomb

def rawPointSegmentLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) : ℝ := rawPointPathLength a y (lineMap x z) 0 1

theorem rawPointSegmentLength_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) : 0 ≤ rawPointSegmentLength a y x z :=
  rawPointPathLength_nonneg a y _ (by norm_num)

theorem rawPointSegmentLength_eq_integral {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) : rawPointSegmentLength a y x z =
      ∫ t in (0 : ℝ)..1, rawPointWeight a y (lineMap x z t) * ‖z - x‖ := by
  unfold rawPointSegmentLength rawPointPathLength
  congr 1
  funext t
  rw [hasDerivAt_lineMap.deriv]

theorem pointDoubleEDist_le_segmentLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist (fun j => 2 * a j) y x z ≤
      ENNReal.ofReal (rawPointSegmentLength a y x z) := by
  have h := pointSmoothConformalEDist_le_path (fun j => 2 * a j) y
    (contDiff_lineMap x z : ContDiff ℝ 1 (lineMap x z)).contDiffOn
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [pointDoublePathELength_eq_rawPointPathLength ha y (contDiff_lineMap x z) (by norm_num)] at h
  simpa only [lineMap_apply_zero, lineMap_apply_one, rawPointSegmentLength] using h

theorem point_weighted_hausdorff_segment {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z) :
    (∫⁻ w in (lineMap x z) '' Icc (0 : ℝ) 1, ENNReal.ofReal (rawPointWeight a y w)
      ∂(Measure.euclideanHausdorffMeasure 1)) = ENNReal.ofReal (rawPointSegmentLength a y x z) := by
  apply point_weighted_hausdorff_length_regular_arc ha y (contDiff_lineMap x z)
    (by norm_num) (lineMap_injective ℝ hxz).injOn
  intro t _
  rw [hasDerivAt_lineMap.deriv]
  exact sub_ne_zero.mpr hxz.symm

end RepulsiveCoulomb
