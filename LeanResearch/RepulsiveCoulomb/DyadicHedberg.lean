module

public import LeanResearch.RepulsiveCoulomb.DyadicSeriesScale

@[expose] public section

/-! The optimized dyadic split, including the regime where the balancing
radius is outside the initial ball. The zero-energy cases are separate. -/
noncomputable section
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem dyadic_series_hedberg {b : ℕ → ℝ≥0∞} {A B k : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hk : 2 ≤ k)
    (ha : ∀ n, b n ≤ ENNReal.ofReal (A * (1 / 2 : ℝ) ^ n))
    (hb : ∀ n, b n ≤ ENNReal.ofReal (B * ((2 : ℝ) ^ (k - 1)) ^ n)) :
    ∑' n, b n ≤ ENNReal.ofReal (5 * A / (A / B) ^ (1 / k)) := by
  have hk0 : 0 < k := by linarith
  have hx0 : 0 < (A / B) ^ (1 / k) := Real.rpow_pos_of_pos (div_pos hA hB) _
  by_cases hAB : B ≤ A
  · apply dyadic_series_balanced_scale hA.le hB.le hk
      (Real.one_le_rpow ((le_div_iff₀ hB).mpr (by simpa using hAB)) (by positivity)) ?_ ha hb
    rw [one_div, Real.rpow_inv_rpow (div_nonneg hA.le hB.le) hk0.ne', mul_div_cancel₀ _ hB.ne']
  · have hx1 : (A / B) ^ (1 / k) ≤ 1 := Real.rpow_le_one (div_nonneg hA.le hB.le)
      ((div_le_one hB).mpr (le_of_lt (lt_of_not_ge hAB))) (by positivity)
    have hs : HasSum (fun n : ℕ => A * (1 / 2 : ℝ) ^ n) (2 * A) := by
      convert hasSum_geometric_two.mul_left A using 1 <;> ring
    calc
      _ ≤ ∑' n, ENNReal.ofReal (A * (1 / 2 : ℝ) ^ n) := ENNReal.tsum_le_tsum ha
      _ = ENNReal.ofReal (2 * A) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
      _ ≤ _ := ENNReal.ofReal_le_ofReal ((le_div_iff₀ hx0).mpr (by nlinarith))

theorem dyadic_series_zero_of_zero_bound {b : ℕ → ℝ≥0∞}
    (hb : ∀ n, b n ≤ 0) : ∑' n, b n = 0 := by
  have he : b = fun _ => 0 := funext (fun n => le_antisymm (hb n) bot_le)
  simp [he]

end RepulsiveCoulomb
