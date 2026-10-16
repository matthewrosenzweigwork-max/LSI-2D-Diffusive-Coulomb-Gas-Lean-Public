module

public import LeanResearch.RepulsiveCoulomb.MetricMidpointGrid
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section

/-! Dyadic floor parameters and their convergence. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def metricDyadicIndex (n : ℕ) (t : ℝ) : ℕ := ⌊(2 : ℝ) ^ n * t⌋₊

theorem metricDyadicIndex_le (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    metricDyadicIndex n t ≤ 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_of_le_one_right (by positivity) ht

theorem metricDyadicIndex_div_two (n : ℕ) (t : ℝ) :
    metricDyadicIndex (n + 1) t / 2 = metricDyadicIndex n t := by
  unfold metricDyadicIndex
  rw [pow_succ', mul_assoc]
  exact Nat.cast_mul_floor_div_cancel (by norm_num : (2 : ℕ) ≠ 0) _

theorem metricDyadicIndex_mono (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    metricDyadicIndex n s ≤ metricDyadicIndex n t :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left hst (by positivity))

theorem metricDyadicIndex_scaled_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n ↦ (metricDyadicIndex n t : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 t) := by
  have hz : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n : ℕ ↦ t - (1 / 2 : ℝ) ^ n) atTop (𝓝 t) by simpa using tendsto_const_nhds.sub hz)
    tendsto_const_nhds
  · intro n
    change t - (1 / 2 : ℝ) ^ n ≤ (metricDyadicIndex n t : ℝ) / (2 : ℝ) ^ n
    rw [hpow]
    have h := Nat.lt_floor_add_one ((2 : ℝ) ^ n * t)
    change (2 : ℝ) ^ n * t < (metricDyadicIndex n t : ℝ) + 1 at h
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
    have he : (t - 1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = (2 : ℝ) ^ n * t - 1 := by field_simp
    rw [he]
    linarith
  · intro n
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
    simpa [metricDyadicIndex, mul_comm] using Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) ht)

end RepulsiveCoulomb
