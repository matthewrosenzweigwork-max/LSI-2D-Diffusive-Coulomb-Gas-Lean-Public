module

public import LeanResearch.RepulsiveCoulomb.AnnularIntegratedEnergy
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Configuration-free bounded overlap of the actual enlarged dyadic annuli. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb
attribute [local instance] Classical.propDecidable

def dyadicScoreRadius (R : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ k * R

theorem dyadicScoreRadius_pos {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 < dyadicScoreRadius R k := mul_pos (by positivity) hR

theorem dyadicScoreAnnuli_index_gap {R : ℝ} (hR : 0 < R) {i j : ℕ} {x : ℂ}
    (hi : x ∈ enlargedScoreAnnulus (dyadicScoreRadius R i))
    (hj : x ∈ enlargedScoreAnnulus (dyadicScoreRadius R j)) : j < i + 3 := by
  by_contra h
  have hij : i + 3 ≤ j := by omega
  have hp : (2 : ℝ) ^ (i + 3) ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hij
  have hm := mul_le_mul_of_nonneg_right hp hR.le
  dsimp [enlargedScoreAnnulus, dyadicScoreRadius] at hi hj
  rw [pow_add] at hm
  norm_num at hm
  linarith [hi.2, hj.1]

theorem dyadicScoreAnnuli_card_le_three {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) (x : ℂ) :
    (s.filter (fun k => x ∈ enlargedScoreAnnulus (dyadicScoreRadius R k))).card ≤ 3 := by
  classical
  let t := s.filter (fun k => x ∈ enlargedScoreAnnulus (dyadicScoreRadius R k))
  change t.card ≤ 3
  by_cases ht : t.Nonempty
  · have hs : t ⊆ Finset.Ico (t.min' ht) (t.min' ht + 3) := by
      intro j hj
      apply Finset.mem_Ico.mpr
      refine ⟨Finset.min'_le _ _ hj, ?_⟩
      exact dyadicScoreAnnuli_index_gap hR
        (Finset.mem_filter.mp (Finset.min'_mem t ht)).2 (Finset.mem_filter.mp hj).2
    have hc := Finset.card_le_card hs
    simpa using hc
  · simp [Finset.not_nonempty_iff_eq_empty.mp ht]

theorem dyadicScoreAnnuli_radius_sq_sum_le {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) (x : ℂ) :
    ∑ k ∈ s.filter (fun k => x ∈ enlargedScoreAnnulus (dyadicScoreRadius R k)),
      (dyadicScoreRadius R k) ^ 2 ≤ 12 * ‖x‖ ^ 2 := by
  classical
  let t := s.filter (fun k => x ∈ enlargedScoreAnnulus (dyadicScoreRadius R k))
  have hb : ∀ k ∈ t, (dyadicScoreRadius R k) ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
    intro k hk
    have hx := (Finset.mem_filter.mp hk).2
    have hr := dyadicScoreRadius_pos hR k
    have hh : dyadicScoreRadius R k ≤ 2 * ‖x‖ := by linarith [hx.1]
    have hs := mul_self_le_mul_self hr.le hh
    nlinarith
  have hc : (t.card : ℝ) ≤ 3 := by exact_mod_cast dyadicScoreAnnuli_card_le_three hR s x
  calc
    _ ≤ ∑ _k ∈ t, 4 * ‖x‖ ^ 2 := Finset.sum_le_sum hb
    _ = (t.card : ℝ) * (4 * ‖x‖ ^ 2) := by simp
    _ ≤ 3 * (4 * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end RepulsiveCoulomb
