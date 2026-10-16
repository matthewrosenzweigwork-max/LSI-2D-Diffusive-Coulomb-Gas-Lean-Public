module

public import LeanResearch.RepulsiveCoulomb.SmoothDyadicTruncation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! A finite logarithmically weighted smooth dyadic layer bound. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

theorem square_log_le_dyadic_height (n : ℕ) {t : ℝ} (ht : |t| ≤ (2 : ℝ) ^ n) :
    t ^ 2 * Real.log (t ^ 2) ≤ (2 * (n : ℝ) * Real.log 2) * t ^ 2 := by
  by_cases hz : t = 0
  · simp [hz]
  have hsq : t ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by nlinarith [sq_abs t, mul_self_le_mul_self (abs_nonneg t) ht]
  have hl : Real.log (t ^ 2) ≤ 2 * (n : ℝ) * Real.log 2 := by
    calc
      _ ≤ Real.log (((2 : ℝ) ^ n) ^ 2) := Real.log_le_log (sq_pos_of_ne_zero hz) hsq
      _ = _ := by rw [Real.log_pow, Real.log_pow]; push_cast; ring
  have h := mul_le_mul_of_nonneg_left hl (sq_nonneg t)
  nlinarith only [h]

theorem smooth_truncation_pair_plateau {a t : ℝ} (ha : 0 < a) (ht : 2 * a ≤ |t|) :
    a ^ 2 ≤ (smoothDyadicTruncation a t) ^ 2 + (smoothDyadicTruncation a (-t)) ^ 2 := by
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0] at ht
    rw [smoothDyadicTruncation_eq_height ha ht]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge ht0)] at ht
    rw [smoothDyadicTruncation_eq_height ha ht]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem finite_dyadic_entropy_layer (N : ℕ) (t : ℝ) (ht : |t| ≤ (2 : ℝ) ^ (N + 2)) :
    t ^ 2 * Real.log (t ^ 2) ≤ 4 * Real.log 2 * t ^ 2 + 96 * Real.log 2 *
      ∑ k ∈ Finset.range N, ((k : ℝ) + 1) *
        ((smoothDyadicTruncation ((2 : ℝ) ^ (k + 1)) t) ^ 2 +
          (smoothDyadicTruncation ((2 : ℝ) ^ (k + 1)) (-t)) ^ 2) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsum (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range n, ((k : ℝ) + 1) *
      ((smoothDyadicTruncation ((2 : ℝ) ^ (k + 1)) t) ^ 2 +
        (smoothDyadicTruncation ((2 : ℝ) ^ (k + 1)) (-t)) ^ 2) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  induction N with
  | zero =>
      have h := square_log_le_dyadic_height 2 ht
      simp only [Finset.sum_range_zero, mul_zero, add_zero]
      convert h using 1 <;> norm_num <;> ring
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hsmall : |t| ≤ (2 : ℝ) ^ (N + 2)
      · have h := ih hsmall
        have hp : 0 ≤ ((N : ℝ) + 1) *
            ((smoothDyadicTruncation ((2 : ℝ) ^ (N + 1)) t) ^ 2 +
              (smoothDyadicTruncation ((2 : ℝ) ^ (N + 1)) (-t)) ^ 2) := by positivity
        nlinarith [mul_nonneg hl2.le hp]
      · let a : ℝ := (2 : ℝ) ^ (N + 1)
        have ha : 0 < a := by dsimp [a]; positivity
        have hpa : (2 : ℝ) ^ (N + 2) = 2 * a := by dsimp [a]; rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]; ring
        have hpb : (2 : ℝ) ^ (N + 1 + 2) = 4 * a := by dsimp [a]; rw [pow_add]; norm_num; ring
        have hplateau := smooth_truncation_pair_plateau ha (show 2 * a ≤ |t| by rw [← hpa]; linarith)
        have htsq : t ^ 2 ≤ 16 * a ^ 2 := by rw [hpb] at ht; nlinarith [sq_abs t]
        have hlog := square_log_le_dyadic_height (N + 1 + 2) ht
        have hcoef : 0 ≤ 2 * ((N + 1 + 2 : ℕ) : ℝ) * Real.log 2 := by positivity
        have hu := hlog.trans (mul_le_mul_of_nonneg_left htsq hcoef)
        have hnc : 32 * ((N + 1 + 2 : ℕ) : ℝ) ≤ 96 * ((N : ℝ) + 1) := by push_cast; nlinarith
        have hc := mul_le_mul_of_nonneg_right hnc (mul_nonneg hl2.le (sq_nonneg a))
        have hp := mul_le_mul_of_nonneg_left hplateau
          (show 0 ≤ 96 * Real.log 2 * ((N : ℝ) + 1) by positivity)
        have hz := mul_nonneg (show 0 ≤ 96 * Real.log 2 by positivity) (hsum N)
        have ht0 := mul_nonneg (show 0 ≤ 4 * Real.log 2 by positivity) (sq_nonneg t)
        change a ^ 2 ≤ _ at hplateau
        change t ^ 2 * Real.log (t ^ 2) ≤ 4 * Real.log 2 * t ^ 2 + 96 * Real.log 2 *
          ((∑ k ∈ Finset.range N, ((k : ℝ) + 1) *
            ((smoothDyadicTruncation ((2 : ℝ) ^ (k + 1)) t) ^ 2 +
              (smoothDyadicTruncation ((2 : ℝ) ^ (k + 1)) (-t)) ^ 2)) +
            ((N : ℝ) + 1) * ((smoothDyadicTruncation a t) ^ 2 + (smoothDyadicTruncation a (-t)) ^ 2))
        nlinarith only [hu, hc, hp, hz, ht0]

end RepulsiveCoulomb
