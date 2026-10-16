module

public import LeanResearch.RepulsiveCoulomb.HolomorphicLocalL2

@[expose] public section

/-! Quantitative nested disks that avoid the puncture without extra separation hypotheses. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem complex_norm_bounds_of_closedBall {c z : ℂ} {r : ℝ} (hz : z ∈ closedBall c r) :
    ‖c‖ - r ≤ ‖z‖ ∧ ‖z‖ ≤ ‖c‖ + r := by
  have hd : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have h1 : ‖c‖ ≤ ‖z‖ + ‖z - c‖ := by
    calc
      ‖c‖ = ‖z - (z - c)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
    calc
      ‖z‖ = ‖c + (z - c)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  constructor <;> linarith

theorem punctured_centered_ball_subset {c : ℂ} {R : ℝ} (hc : c ≠ 0) (hR : ‖c‖ < R / 2) :
    ball c (‖c‖ / 2) ⊆ ball (0 : ℂ) R \ {0} := by
  intro z hz
  have hb := complex_norm_bounds_of_closedBall (ball_subset_closedBall hz)
  have hp := norm_pos_iff.mpr hc
  refine ⟨?_, ?_⟩
  · simp only [mem_ball, dist_zero_right]
    linarith
  · simp only [mem_singleton_iff]
    intro he
    rw [he, norm_zero] at hb
    linarith [hb.1]

theorem puncture_local_closedBall_subset {c : ℂ} (hc : c ≠ 0) :
    closedBall c (‖c‖ / 4) ⊆ ball (0 : ℂ) (2 * ‖c‖) := by
  intro z hz
  have hb := complex_norm_bounds_of_closedBall hz
  have hp := norm_pos_iff.mpr hc
  simp only [mem_ball, dist_zero_right]
  linarith [hb.2]

theorem puncture_local_norm_lower {c z : ℂ} (hz : z ∈ closedBall c (‖c‖ / 4)) :
    ‖c‖ ≤ 2 * ‖z‖ := by
  have hb := complex_norm_bounds_of_closedBall hz
  nlinarith [hb.1, norm_nonneg c]

theorem puncture_local_closedBall_avoids {c : ℂ} {R : ℝ} (hc : c ≠ 0) (hR : ‖c‖ < R / 2) :
    closedBall c (‖c‖ / 4) ⊆ ball (0 : ℂ) R \ {0} := by
  apply (closedBall_subset_ball (by have hp := norm_pos_iff.mpr hc; linarith : ‖c‖ / 4 < ‖c‖ / 2)).trans
  exact punctured_centered_ball_subset hc hR

end RepulsiveCoulomb
