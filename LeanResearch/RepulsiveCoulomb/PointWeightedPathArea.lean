module

public import LeanResearch.RepulsiveCoulomb.PointSquaredWeightRadius
public import LeanResearch.RepulsiveCoulomb.PointConformalApproximateMidpoint
public import LeanResearch.RepulsiveCoulomb.PointMetricVolume

@[expose] public section

/-! The doubled-exponent metric controls squared-weight area by actual raw-weighted
smooth path length. This is a geometric input, not the relative separator theorem. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointConformalDensity_double_exponents {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (z : ℂ) :
    pointConformalDensity (fun j => 2 * a j) y z = rawPointWeight a y z := by
  rw [pointConformalDensity, rawPointWeight_double_exponents,
    Real.sqrt_sq (rawPointWeight_nonneg a y z)]

def rawPointPathLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (s t : ℝ) : ℝ :=
  ∫ u in s..t, rawPointWeight a y (γ u) * ‖deriv γ u‖

theorem rawPointPathLength_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) {s t : ℝ} (hst : s ≤ t) : 0 ≤ rawPointPathLength a y γ s t := by
  exact intervalIntegral.integral_nonneg hst
    (fun u _ => mul_nonneg (rawPointWeight_nonneg a y _) (norm_nonneg _))

theorem pointDoublePathELength_eq_rawPointPathLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) {s t : ℝ} (hst : s ≤ t) :
    pointConformalPathELength (fun j => 2 * a j) y γ s t =
      ENNReal.ofReal (rawPointPathLength a y γ s t) := by
  rw [pointConformalPathELength_eq_integral (fun j => mul_nonneg (by norm_num) (ha j)) y hγ hst]
  simp only [pointConformalDensity_double_exponents, rawPointPathLength]

theorem pointDoubleEDist_le_rawPointPathLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) {s t : ℝ} (hst : s ≤ t) :
    (pointSmoothConformalEDist (fun j => 2 * a j) y (γ s) (γ t)).toReal ≤
      rawPointPathLength a y γ s t := by
  have h := pointSmoothConformalEDist_le_path (fun j => 2 * a j) y hγ.contDiffOn hst
  rw [pointDoublePathELength_eq_rawPointPathLength ha y hγ hst] at h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (rawPointPathLength_nonneg a y γ hst)] using ht

theorem pointSquaredBallArea_le_rawPointPathLength_sq {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hst : s ≤ t) :
    (rawPointMeasure (fun j => 2 * a j) y).real (ball (γ s) ‖γ t - γ s‖) ≤
      Real.pi * Real.exp (8 * Q) * rawPointPathLength a y γ s t ^ 2 := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hQ2 : ∑ j, 2 * a j ≤ 2 * Q := by rw [← Finset.mul_sum]; linarith
  rw [rawPointMeasure_ball_real_eq_integral ha2]
  have hb := ballIntegral_le_pointConformalEDist_sq ha2 hQ2 y (γ s) (γ t)
  have hd := pointDoubleEDist_le_rawPointPathLength ha y hγ hst
  have hs : (pointSmoothConformalEDist (fun j => 2 * a j) y (γ s) (γ t)).toReal ^ 2 ≤
      rawPointPathLength a y γ s t ^ 2 := by
    have hn := ENNReal.toReal_nonneg (a := pointSmoothConformalEDist (fun j => 2 * a j) y (γ s) (γ t))
    nlinarith
  have he : 4 * (2 * Q) = 8 * Q := by ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end RepulsiveCoulomb
