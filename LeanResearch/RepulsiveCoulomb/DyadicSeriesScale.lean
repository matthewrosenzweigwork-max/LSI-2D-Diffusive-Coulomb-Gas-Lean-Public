import LeanResearch.RepulsiveCoulomb.DyadicSeriesSplit
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Quantitative choice of the splitting radius for the dyadic Sobolev series. -/
noncomputable section
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem dyadic_series_balanced_scale {b : ℕ → ℝ≥0∞} {A B k x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : 2 ≤ k) (hx : 1 ≤ x)
    (hbalance : B * x ^ k = A)
    (ha : ∀ n, b n ≤ ENNReal.ofReal (A * (1 / 2 : ℝ) ^ n))
    (hb : ∀ n, b n ≤ ENNReal.ofReal (B * ((2 : ℝ) ^ (k - 1)) ^ n)) :
    ∑' n, b n ≤ ENNReal.ofReal (5 * A / x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  obtain ⟨N, hN, hN'⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hv : (2 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ k - 1 by linarith)
  have hp : B * ((2 : ℝ) ^ (k - 1)) ^ N ≤ A / x := by
    have he : ((2 : ℝ) ^ (k - 1)) ^ N = ((2 : ℝ) ^ N) ^ (k - 1) := by
      rw [← Real.rpow_mul_natCast (by norm_num), mul_comm, Real.rpow_natCast_mul (by norm_num)]
    rw [he]
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hN (by linarith)) hB).trans
    apply le_of_eq
    apply (eq_div_iff hx0.ne').mpr
    rw [mul_assoc, ← Real.rpow_add_one hx0.ne' (k - 1)]
    simpa only [sub_add_cancel] using hbalance
  have ht : 2 * A * (1 / 2 : ℝ) ^ N ≤ 4 * A / x := by
    rw [div_pow, one_pow, mul_one_div]
    apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) N) hx0).mpr
    rw [pow_succ] at hN'
    nlinarith [mul_le_mul_of_nonneg_left hN'.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)]
  apply (dyadic_series_split hA hB hv ha hb N).trans
  apply ENNReal.ofReal_le_ofReal
  have he : A / x + 4 * A / x = 5 * A / x := by ring
  exact he ▸ add_le_add hp ht

end RepulsiveCoulomb
