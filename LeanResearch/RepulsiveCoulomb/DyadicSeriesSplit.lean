module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-! Explicit elementary split bounds for the dyadic series in the local
Sobolev argument. No analytic hypothesis is hidden in these scalar estimates. -/
noncomputable section
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem geometric_prefix_le_power {v : ℝ} (hv : 2 ≤ v) (N : ℕ) :
    ∑ n ∈ Finset.range N, v ^ n ≤ v ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 ≤ v ^ N := pow_nonneg (by linarith) N
    nlinarith

theorem dyadic_series_split {b : ℕ → ℝ≥0∞} {A B v : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : 2 ≤ v)
    (ha : ∀ n, b n ≤ ENNReal.ofReal (A * (1 / 2 : ℝ) ^ n))
    (hb : ∀ n, b n ≤ ENNReal.ofReal (B * v ^ n)) (N : ℕ) :
    ∑' n, b n ≤ ENNReal.ofReal (B * v ^ N + 2 * A * (1 / 2 : ℝ) ^ N) := by
  have hp : (∑ n ∈ Finset.range N, b n) ≤ ENNReal.ofReal (B * v ^ N) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (B * v ^ n) := Finset.sum_le_sum (fun n _ => hb n)
      _ = ENNReal.ofReal (B * ∑ n ∈ Finset.range N, v ^ n) := by
        have he := ENNReal.ofReal_sum_of_nonneg
          (s := Finset.range N) (f := fun n : ℕ => B * v ^ n)
          (fun n _ => mul_nonneg hB (pow_nonneg (by linarith) n))
        rw [← he, Finset.mul_sum]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (geometric_prefix_le_power hv N) hB)
  have ht : (∑' n, b (n + N)) ≤ ENNReal.ofReal (2 * A * (1 / 2 : ℝ) ^ N) := by
    have hs : HasSum (fun n : ℕ => A * (1 / 2 : ℝ) ^ (n + N)) (2 * A * (1 / 2 : ℝ) ^ N) := by
      convert hasSum_geometric_two.mul_left (A * (1 / 2 : ℝ) ^ N) using 1
      · ext n
        rw [pow_add]
        ring
      · ring
    calc
      _ ≤ ∑' n, ENNReal.ofReal (A * (1 / 2 : ℝ) ^ (n + N)) := ENNReal.tsum_le_tsum (fun n => ha (n + N))
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
  have hsplit := Summable.sum_add_tsum_nat_add' (f := b) (k := N) ENNReal.summable
  calc
    _ = (∑ n ∈ Finset.range N, b n) + ∑' n, b (n + N) :=
      hsplit.symm
    _ ≤ ENNReal.ofReal (B * v ^ N) + ENNReal.ofReal (2 * A * (1 / 2 : ℝ) ^ N) := add_le_add hp ht
    _ = _ := (ENNReal.ofReal_add (show 0 ≤ B * v ^ N from mul_nonneg hB (pow_nonneg (by linarith) N))
      (show 0 ≤ 2 * A * (1 / 2 : ℝ) ^ N by positivity)).symm

end RepulsiveCoulomb
