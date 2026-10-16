import LeanResearch.RepulsiveCoulomb.CoulombFormApproximation
import LeanResearch.RepulsiveCoulomb.PoleBranchRealLpMean

/-! RECORDS-ONLY UNCHECKED DRAFT. Quantitative selection from the original
smooth core; no subtraction of constants from a core function is performed. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombFormValue_norm_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) : ‖coulombFormValueL N hβ u‖ ≤ ‖u‖ := by
  have h := coulombForm_norm_sq N hβ u
  unfold coulombFormEnergy at h
  nlinarith [norm_nonneg u, norm_nonneg (coulombFormValueL N hβ u),
    sq_nonneg ‖coulombFormGradientL N hβ u‖]

theorem coulombFormGradient_norm_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) : ‖coulombFormGradientL N hβ u‖ ≤ ‖u‖ := by
  have h := coulombForm_norm_sq N hβ u
  unfold coulombFormEnergy at h
  nlinarith [norm_nonneg u, norm_nonneg (coulombFormGradientL N hβ u),
    sq_nonneg ‖coulombFormValueL N hβ u‖]

theorem coulombFormCore_exists_norm_error (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : TestFunction (coulombDomain N) ℝ ⊤,
      ‖coulombFormCore hβ φ - u‖ < ε := by
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation N hβ u
  have he := hφ.eventually (Metric.ball_mem_nhds u hε)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨φ n, by simpa only [Metric.mem_ball, dist_eq_norm] using hn⟩

theorem coulombFormCore_error_components (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    {ε : ℝ} (hε : ‖coulombFormCore hβ φ - u‖ < ε) :
    ‖coulombFormValueL N hβ (coulombFormCore hβ φ) - coulombFormValueL N hβ u‖ < ε ∧
    ‖coulombFormGradientL N hβ (coulombFormCore hβ φ) - coulombFormGradientL N hβ u‖ < ε := by
  constructor
  · simpa only [map_sub] using
      (coulombFormValue_norm_le N hβ (coulombFormCore hβ φ - u)).trans_lt hε
  · simpa only [map_sub] using
      (coulombFormGradient_norm_le N hβ (coulombFormCore hβ φ - u)).trans_lt hε

end RepulsiveCoulomb
