module

public import LeanResearch.RepulsiveCoulomb.PointConformalMidpoint
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Consistent dyadic metric subdivisions, constructed from exact midpoints.
This is generic infrastructure for the geodesic construction, not an additional
analytic hypothesis on the point model. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

variable {X : Type*}

def metricMidpointGrid (μ : X → X → X) (x z : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else z
  | n + 1, k => if k % 2 = 0 then metricMidpointGrid μ x z n (k / 2)
      else μ (metricMidpointGrid μ x z n (k / 2)) (metricMidpointGrid μ x z n (k / 2 + 1))

theorem metricMidpointGrid_even (μ : X → X → X) (x z : X) (n k : ℕ) :
    metricMidpointGrid μ x z (n + 1) (2 * k) = metricMidpointGrid μ x z n k := by
  simp [metricMidpointGrid]

theorem metricMidpointGrid_odd (μ : X → X → X) (x z : X) (n k : ℕ) :
    metricMidpointGrid μ x z (n + 1) (2 * k + 1) =
      μ (metricMidpointGrid μ x z n k) (metricMidpointGrid μ x z n (k + 1)) := by
  simp [metricMidpointGrid, Nat.add_div]

theorem metricMidpointGrid_zero (μ : X → X → X) (x z : X) (n : ℕ) :
    metricMidpointGrid μ x z n 0 = x := by
  induction n with
  | zero => simp [metricMidpointGrid]
  | succ n ih => simpa [metricMidpointGrid] using ih

theorem metricMidpointGrid_last (μ : X → X → X) (x z : X) (n : ℕ) :
    metricMidpointGrid μ x z n (2 ^ n) = z := by
  induction n with
  | zero => simp [metricMidpointGrid]
  | succ n ih => rw [pow_succ', metricMidpointGrid_even, ih]

variable [MetricSpace X]

theorem metricMidpointGrid_adjacent (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (n k : ℕ) (hk : k < 2 ^ n) :
    dist (metricMidpointGrid μ x z n k) (metricMidpointGrid μ x z n (k + 1)) =
      dist x z / (2 : ℝ) ^ n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst k
    simp [metricMidpointGrid]
  | succ n ih =>
    have hdiv : k / 2 < 2 ^ n := by rw [pow_succ'] at hk; omega
    rcases Nat.mod_two_eq_zero_or_one k with he | ho
    · have hk' : k = 2 * (k / 2) := by omega
      rw [hk', metricMidpointGrid_even, metricMidpointGrid_odd, (hμ _ _).1, ih _ hdiv, pow_succ]
      ring
    · have hk' : k = 2 * (k / 2) + 1 := by omega
      have hs : k + 1 = 2 * (k / 2 + 1) := by omega
      rw [hs, metricMidpointGrid_even]
      conv_lhs => arg 1; rw [hk', metricMidpointGrid_odd]
      rw [(hμ _ _).2, ih _ hdiv, pow_succ]
      ring

theorem metricMidpointGrid_dist_le (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ 2 ^ n) :
    dist (metricMidpointGrid μ x z n i) (metricMidpointGrid μ x z n j) ≤
      (j - i : ℕ) * (dist x z / (2 : ℝ) ^ n) := by
  have h := dist_le_Ico_sum_dist (metricMidpointGrid μ x z n) hij
  calc
    _ ≤ ∑ k ∈ Finset.Ico i j, dist (metricMidpointGrid μ x z n k)
        (metricMidpointGrid μ x z n (k + 1)) := h
    _ = _ := by
      simp_rw [Finset.sum_congr rfl (fun k hk ↦ metricMidpointGrid_adjacent μ hμ x z n k
        ((Finset.mem_Ico.mp hk).2.trans_le hj))]
      simp

theorem metricMidpointGrid_dist_eq (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ 2 ^ n) :
    dist (metricMidpointGrid μ x z n i) (metricMidpointGrid μ x z n j) =
      ((j : ℝ) - i) * (dist x z / (2 : ℝ) ^ n) := by
  have hupper := metricMidpointGrid_dist_le μ hμ x z n i j hij hj
  rw [Nat.cast_sub hij] at hupper
  apply le_antisymm hupper
  have hleft := metricMidpointGrid_dist_le μ hμ x z n 0 i (Nat.zero_le _) (hij.trans hj)
  have hright := metricMidpointGrid_dist_le μ hμ x z n j (2 ^ n) hj le_rfl
  rw [metricMidpointGrid_zero, Nat.sub_zero] at hleft
  rw [metricMidpointGrid_last, Nat.cast_sub hj, Nat.cast_pow, Nat.cast_ofNat] at hright
  have htri := (dist_triangle x (metricMidpointGrid μ x z n i) z).trans
    (add_le_add le_rfl (dist_triangle (metricMidpointGrid μ x z n i)
      (metricMidpointGrid μ x z n j) z))
  have hcancel : (2 : ℝ) ^ n * (dist x z / (2 : ℝ) ^ n) = dist x z := by
    field_simp
  nlinarith

end RepulsiveCoulomb
