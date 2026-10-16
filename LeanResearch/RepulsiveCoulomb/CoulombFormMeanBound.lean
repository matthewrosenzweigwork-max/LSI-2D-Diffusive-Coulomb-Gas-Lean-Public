module

public import LeanResearch.RepulsiveCoulomb.CoulombCoreApproximationError

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. Uniform norm-one mean functional and
mean errors under genuine original-core approximation. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombRealOne_norm (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ‖poleBranchRealOne N hβ‖ = 1 := by
  have h := poleBranchRealMean_one N hβ
  change inner ℝ (poleBranchRealOne N hβ) (poleBranchRealOne N hβ) = 1 at h
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (poleBranchRealOne N hβ)]

theorem coulombRealMean_norm_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : Lp ℝ 2 (coulombMeasure N β)) : |poleBranchRealMean N hβ u| ≤ ‖u‖ := by
  change |inner ℝ (poleBranchRealOne N hβ) u| ≤ ‖u‖
  simpa only [coulombRealOne_norm, one_mul, Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ) (poleBranchRealOne N hβ) u

theorem coulombFormMean_error_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u v : CoulombFormDomain N hβ) :
    |poleBranchRealMean N hβ (coulombFormValueL N hβ u) -
      poleBranchRealMean N hβ (coulombFormValueL N hβ v)| ≤ ‖u - v‖ := by
  have h := (coulombRealMean_norm_le N hβ (coulombFormValueL N hβ (u - v))).trans
    (coulombFormValue_norm_le N hβ (u - v))
  simpa only [map_sub] using h

end RepulsiveCoulomb
