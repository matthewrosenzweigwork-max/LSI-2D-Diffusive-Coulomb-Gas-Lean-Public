module

public import LeanResearch.RepulsiveCoulomb.PointWeightedSegment
public import LeanResearch.RepulsiveCoulomb.PointWeightedRegionArea

@[expose] public section

/-! Uniform area control by the actual sum of weighted edge lengths of a finite
polygonal chain. No global C1 parametrization of a polygon is assumed. -/
noncomputable section
open Set MeasureTheory Metric AffineMap
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def rawPointChainLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p : ℕ → ℂ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, rawPointSegmentLength a y (p i) (p (i + 1))

theorem rawPointChainLength_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p : ℕ → ℂ) (n : ℕ) : 0 ≤ rawPointChainLength a y p n :=
  Finset.sum_nonneg (fun i _ => rawPointSegmentLength_nonneg a y _ _)

theorem rawPointChainLength_mono {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p : ℕ → ℂ) {i n : ℕ} (hin : i ≤ n) :
    rawPointChainLength a y p i ≤ rawPointChainLength a y p n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hin)
  intro j _ _
  exact rawPointSegmentLength_nonneg a y _ _

theorem pointDoubleEDist_le_chainLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℕ → ℂ) (n : ℕ) :
    pointSmoothConformalEDist (fun j => 2 * a j) y (p 0) (p n) ≤
      ENNReal.ofReal (rawPointChainLength a y p n) := by
  induction n with
  | zero => simp [rawPointChainLength, pointSmoothConformalEDist_self]
  | succ n ih =>
    have h := (pointSmoothConformalEDist_triangle (fun j => 2 * a j) y (p 0) (p n) (p (n + 1))).trans
      (add_le_add ih (pointDoubleEDist_le_segmentLength ha y (p n) (p (n + 1))))
    rw [← ENNReal.ofReal_add (rawPointChainLength_nonneg a y p n)
      (rawPointSegmentLength_nonneg a y _ _)] at h
    simpa only [rawPointChainLength, Finset.sum_range_succ] using h

theorem pointSquaredRegionArea_le_chainLength_sq {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) (p : ℕ → ℂ) (n : ℕ) {U : Set ℂ}
    (hU : Bornology.IsBounded U)
    (hcover : ∀ z ∈ frontier U, ∃ i < n, z ∈ (lineMap (p i) (p (i + 1))) '' Icc (0 : ℝ) 1) :
    (rawPointMeasure (fun j => 2 * a j) y).real U ≤
      Real.pi * Real.exp (8 * Q) * rawPointChainLength a y p n ^ 2 := by
  obtain ⟨k, hk, hmax⟩ := (Finset.range (n + 1)).exists_max_image
    (fun i => ‖p i - p 0‖) (by simp)
  have hfront : frontier U ⊆ closedBall (p 0) ‖p k - p 0‖ := by
    intro z hz
    obtain ⟨i, hi, t, ht, rfl⟩ := hcover z hz
    apply (convex_closedBall (p 0) ‖p k - p 0‖).lineMap_mem
    · exact mem_closedBall.mpr (by rw [dist_eq_norm]; exact hmax i (Finset.mem_range.mpr (by omega)))
    · exact mem_closedBall.mpr (by rw [dist_eq_norm]; exact hmax (i + 1) (Finset.mem_range.mpr (by omega)))
    · exact ht
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hQ2 : ∑ j, 2 * a j ≤ 2 * Q := by rw [← Finset.mul_sum]; linarith
  have hsub := subset_closure.trans (planar_closure_subset_closedBall_of_frontier hU _ _ hfront)
  have hm := ENNReal.toReal_mono (rawPointMeasure_closedBall_lt_top ha2 y _ _).ne
    (measure_mono hsub : rawPointMeasure (fun j => 2 * a j) y U ≤ _)
  rw [rawPointMeasure_closedBall ha2, ENNReal.toReal_ofReal
    (integral_nonneg (rawPointWeight_nonneg (fun j => 2 * a j) y))] at hm
  have hb := ballIntegral_le_pointConformalEDist_sq ha2 hQ2 y (p 0) (p k)
  have he : 4 * (2 * Q) = 8 * Q := by ring
  rw [he] at hb
  have hd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (pointDoubleEDist_le_chainLength ha y p k)
  rw [ENNReal.toReal_ofReal (rawPointChainLength_nonneg a y p k)] at hd
  have hn := rawPointChainLength_mono a y p (show k ≤ n by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hnn := ENNReal.toReal_nonneg (a := pointSmoothConformalEDist (fun j => 2 * a j) y (p 0) (p k))
  have hs : (pointSmoothConformalEDist (fun j => 2 * a j) y (p 0) (p k)).toReal ^ 2 ≤
      rawPointChainLength a y p n ^ 2 := by nlinarith
  exact hm.trans (hb.trans (mul_le_mul_of_nonneg_left hs (by positivity)))

end RepulsiveCoulomb
