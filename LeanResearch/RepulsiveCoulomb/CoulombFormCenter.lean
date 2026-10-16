module

public import LeanResearch.RepulsiveCoulomb.CoulombConstantDomain
public import LeanResearch.RepulsiveCoulomb.PoleBranchRealLpMean

@[expose] public section

/-! Actual centering inside the original closed form domain for every
particle number at least two. The full-domain constant is the checked limit
of original-core cutoffs; no compact-core recentering is asserted. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
namespace RepulsiveCoulomb

theorem coulombConstantForm_value_eq_realOne (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombFormValueL (N + 2) hβ (coulombConstantForm N hβ) = poleBranchRealOne (N + 2) hβ := by
  apply Lp.ext
  filter_upwards [coulombConstantForm_value N hβ, poleBranchRealOne_coe (N + 2) hβ] with z h1 h2
  exact h1.trans h2.symm

def coulombFormCenter (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) : CoulombFormDomain (N + 2) hβ :=
  u - poleBranchRealMean (N + 2) hβ (coulombFormValueL (N + 2) hβ u) • coulombConstantForm N hβ

theorem coulombFormCenter_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    coulombFormValueL (N + 2) hβ (coulombFormCenter N hβ u) =
      poleBranchRealCenter (N + 2) hβ (coulombFormValueL (N + 2) hβ u) := by
  simp only [coulombFormCenter, poleBranchRealCenter, map_sub, map_smul,
    coulombConstantForm_value_eq_realOne]

theorem coulombFormCenter_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    coulombFormGradientL (N + 2) hβ (coulombFormCenter N hβ u) = coulombFormGradientL (N + 2) hβ u := by
  simp only [coulombFormCenter, map_sub, map_smul, coulombConstantForm_gradient, smul_zero, sub_zero]

theorem coulombFormCenter_mean (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    poleBranchRealMean (N + 2) hβ (coulombFormValueL (N + 2) hβ (coulombFormCenter N hβ u)) = 0 := by
  rw [coulombFormCenter_value, poleBranchRealCenter_mean]

theorem coulombFormCenter_value_norm_sq (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    ‖coulombFormValueL (N + 2) hβ (coulombFormCenter N hβ u)‖ ^ 2 =
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) := by
  rw [coulombFormCenter_value, poleBranchRealCenter_norm_sq]

end RepulsiveCoulomb
