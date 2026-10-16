module

public import LeanResearch.RepulsiveCoulomb.PointLocalMaximalEnergy

@[expose] public section

/-! Explicit growth of the square-root local energy along the dyadic chain.
The dimension is deliberately enlarged to 2(Q+2), giving the target Sobolev
exponent without any endpoint claim. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointLocalEnergy {m : ℕ} (Q : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) (R : ℝ) (g : ℂ → ℝ) : ℝ :=
  rawPointGrowthConstant Q * (∫ z in ball c (11 * R), g z ∂rawPointMeasure a y) /
    (rawPointMeasure a y).real (ball c R)

theorem pointLocalEnergy_nonneg {m : ℕ} (Q : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) (R : ℝ) (g : ℂ → ℝ) (hgn : ∀ z, 0 ≤ g z) :
    0 ≤ pointLocalEnergy Q a y c R g :=
  div_nonneg (mul_nonneg (rawPointGrowthConstant_pos Q).le (integral_nonneg hgn)) ENNReal.toReal_nonneg

theorem dyadicBallRadius_ratio {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    R / dyadicBallRadius R n = (2 : ℝ) ^ n := by
  unfold dyadicBallRadius
  rw [div_pow, one_pow]
  field_simp

theorem pointLocalEnergy_sqrt_average_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ≤
      Real.sqrt (pointLocalEnergy Q a y c R g) * ((2 : ℝ) ^ n) ^ (Q + 2) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have ht : 1 ≤ ((2 : ℝ) ^ n) ^ (Q + 2) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by linarith)
  have hE := pointLocalEnergy_nonneg Q a y c R g hgn
  have h := rawPointMeasure_local_energy_bound ha hQ y hR hx g hg hgn n
  rw [dyadicBallRadius_ratio (show 2 * R ≠ 0 by positivity)] at h
  have he : (rawPointGrowthConstant Q * ((2 : ℝ) ^ n) ^ (Q + 2)) *
      (∫ z in ball c (11 * R), g z ∂rawPointMeasure a y) /
      (rawPointMeasure a y).real (ball c R) =
      pointLocalEnergy Q a y c R g * ((2 : ℝ) ^ n) ^ (Q + 2) := by
    unfold pointLocalEnergy
    ring
  rw [he] at h
  apply (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) (by positivity))).mpr
  rw [mul_pow, Real.sq_sqrt hE]
  exact h.trans (mul_le_mul_of_nonneg_left (by nlinarith :
    ((2 : ℝ) ^ n) ^ (Q + 2) ≤ (((2 : ℝ) ^ n) ^ (Q + 2)) ^ 2) hE)

theorem pointLocalEnergy_scaled_average_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) (n : ℕ) :
    (1 / 2 : ℝ) ^ n * Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ≤
      Real.sqrt (pointLocalEnergy Q a y c R g) * ((2 : ℝ) ^ (Q + 1)) ^ n := by
  have h := mul_le_mul_of_nonneg_left (pointLocalEnergy_sqrt_average_bound ha hQ y hR hx g hg hgn n)
    (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity)
  apply h.trans_eq
  have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : ((2 : ℝ) ^ n) ^ (Q + 2) = ((2 : ℝ) ^ n) ^ (Q + 1) * (2 : ℝ) ^ n := by
    convert Real.rpow_add_one hp (Q + 1) using 1 <;> congr 1 <;> ring
  rw [he, div_pow, one_pow]
  have hc : ((2 : ℝ) ^ n) ^ (Q + 1) = ((2 : ℝ) ^ (Q + 1)) ^ n := by
    rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]
  rw [hc]
  field_simp

end RepulsiveCoulomb
