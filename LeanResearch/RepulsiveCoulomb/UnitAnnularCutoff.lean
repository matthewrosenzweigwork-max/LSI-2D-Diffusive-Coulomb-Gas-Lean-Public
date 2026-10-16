import LeanResearch.RepulsiveCoulomb.PointCutoffBump

/-! One fixed smooth annular cutoff with a strict support margin inside
{1/2 < norm z < 4}. Its rescalings are used in prop:uncertainty. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def innerUnitAnnularBump : ContDiffBump (0 : ℂ) := ⟨3 / 4, 1, by norm_num, by norm_num⟩
def outerUnitAnnularBump : ContDiffBump (0 : ℂ) := ⟨2, 3, by norm_num, by norm_num⟩
def unitAnnularCutoff (z : ℂ) : ℝ := (1 - innerUnitAnnularBump z) * outerUnitAnnularBump z

theorem unitAnnularCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) unitAnnularCutoff :=
  (contDiff_const.sub innerUnitAnnularBump.contDiff).mul outerUnitAnnularBump.contDiff

theorem unitAnnularCutoff_mem_Icc (z : ℂ) : unitAnnularCutoff z ∈ Icc (0 : ℝ) 1 := by
  have hi0 : 0 ≤ innerUnitAnnularBump z := innerUnitAnnularBump.nonneg
  have hi1 : innerUnitAnnularBump z ≤ 1 := innerUnitAnnularBump.le_one
  have ho0 : 0 ≤ outerUnitAnnularBump z := outerUnitAnnularBump.nonneg
  have ho1 : outerUnitAnnularBump z ≤ 1 := outerUnitAnnularBump.le_one
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hi1) ho0
  · change (1 - innerUnitAnnularBump z) * outerUnitAnnularBump z ≤ 1
    nlinarith

theorem unitAnnularCutoff_one {z : ℂ} (hz : 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) : unitAnnularCutoff z = 1 := by
  have hi : innerUnitAnnularBump z = 0 := innerUnitAnnularBump.zero_of_le_dist
    (by simpa only [innerUnitAnnularBump, dist_zero_right] using hz.1)
  have ho : outerUnitAnnularBump z = 1 := outerUnitAnnularBump.one_of_mem_closedBall
    (by simpa only [outerUnitAnnularBump, mem_closedBall, dist_zero_right] using hz.2)
  simp only [unitAnnularCutoff, hi, ho, sub_zero, mul_one]

theorem unitAnnularCutoff_zero_low {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) : unitAnnularCutoff z = 0 := by
  have hi : innerUnitAnnularBump z = 1 := innerUnitAnnularBump.one_of_mem_closedBall
    (by simpa only [innerUnitAnnularBump, mem_closedBall, dist_zero_right] using hz)
  simp only [unitAnnularCutoff, hi, sub_self, zero_mul]

theorem unitAnnularCutoff_zero_high {z : ℂ} (hz : 3 ≤ ‖z‖) : unitAnnularCutoff z = 0 := by
  have ho : outerUnitAnnularBump z = 0 := outerUnitAnnularBump.zero_of_le_dist
    (by simpa only [outerUnitAnnularBump, dist_zero_right] using hz)
  simp only [unitAnnularCutoff, ho, mul_zero]

theorem unitAnnularCutoff_tsupport : tsupport unitAnnularCutoff ⊆ {z : ℂ | 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3} := by
  apply closure_minimal
  · intro z hz
    constructor
    · by_contra h
      exact hz (unitAnnularCutoff_zero_low (le_of_lt (lt_of_not_ge h)))
    · by_contra h
      exact hz (unitAnnularCutoff_zero_high (le_of_lt (lt_of_not_ge h)))
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

theorem unitAnnularCutoff_hasCompactSupport : HasCompactSupport unitAnnularCutoff := by
  change IsCompact (tsupport unitAnnularCutoff)
  apply (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset (isClosed_tsupport unitAnnularCutoff)
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using (unitAnnularCutoff_tsupport hz).2

theorem unitAnnularCutoff_fderiv_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, ‖fderiv ℝ unitAnnularCutoff z‖ ≤ C := by
  have hc := unitAnnularCutoff_contDiff.continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro z
  by_cases hz : z ∈ closedBall (0 : ℂ) 3
  · exact (hB z hz).trans (by linarith [le_abs_self B])
  · have hs : z ∉ tsupport unitAnnularCutoff := by
      intro h
      exact hz (by simpa only [mem_closedBall, dist_zero_right] using (unitAnnularCutoff_tsupport h).2)
    rw [fderiv_of_notMem_tsupport ℝ hs, norm_zero]
    positivity

end RepulsiveCoulomb
