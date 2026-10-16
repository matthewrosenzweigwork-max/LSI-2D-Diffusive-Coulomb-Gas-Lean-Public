module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.AnalyticLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.RelativeLabeledPoincare

@[expose] public section

/-! The original full labeled Poincare theorem. Its new weighted coefficient
is chosen before the particle number; the Gibbs measure and closed physical
form are unchanged. Compact-temperature uniformity fixes a single exponent
cap and uses the actual finite exceptional-family optimal-gap bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb.PaperRoute

def paperCAll {β : ℝ} (hβ : 0 < β) : ℝ :=
  poleBranchSymmetricPoincareConstant hβ + paperCrel β

theorem paperCAll_pos {β : ℝ} (hβ : 0 < β) : 0 < paperCAll hβ :=
  add_pos (poleBranchSymmetricPoincareConstant_pos hβ) (paperCrel_pos hβ)

/-- Exact original theorem: every real full-form observable and every N >= 2. -/
theorem paper_full_labeled_poincare {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (poleBranchSymmetricPoincareConstant hβ + paperCrel β) * coulombFormEnergy N hβ u := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hlabel := paper_variance_reduction hβ n u
  rw [coulombFormSymmetrizer_value] at hlabel
  have hs := paper_symmetrized_poincare (by omega : 2 ≤ n + 2) hβ u
  have h := hlabel.trans (add_le_add hs
    (le_rfl : paperCrel β * coulombFormEnergy (n + 2) hβ u ≤ _))
  simpa only [add_mul] using h

/-- On the literal real smooth core, the energy is the physical gradient integral. -/
theorem paper_full_labeled_poincare_core {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    variance (φ : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (poleBranchSymmetricPoincareConstant hβ + paperCrel β) *
        (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) := by
  have h := paper_full_labeled_poincare hβ N hN (coulombFormCore hβ φ)
  rw [variance_congr (coulombFormCore_value hβ φ), coulombFormCore_energy_eq_integral] at h
  exact h

/-- The named constant has no N parameter and no coefficient is silently enlarged. -/
theorem paper_full_labeled_poincare_named {β : ℝ} (hβ : 0 < β) :
    0 < paperCAll hβ ∧ ∀ (N : ℕ), 2 ≤ N → ∀ u : CoulombFormDomain N hβ,
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        paperCAll hβ * coulombFormEnergy N hβ u :=
  ⟨paperCAll_pos hβ, paper_full_labeled_poincare hβ⟩

def paperCAllInterval {a : ℝ} (ha : 0 < a) (b : ℝ) : ℝ :=
  poleBranchSymmetricIntervalSup ha b + paperCrelInterval a b

theorem paperCAllInterval_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < paperCAllInterval ha b :=
  add_pos (poleBranchSymmetricIntervalSup_pos ha hab) (paperCrelInterval_pos ha)

/-- Literal compact-temperature full-domain bound, with one fixed cap 2*b. -/
theorem paper_full_labeled_poincare_compact {a b β : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (poleBranchSymmetricIntervalSup ha b + paperCrelInterval a b) * coulombFormEnergy N hβ u := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hlabel := paper_variance_reduction_interval ha hβ hlo hhi n u
  rw [coulombFormSymmetrizer_value] at hlabel
  have hs := paper_symmetrized_poincare (by omega : 2 ≤ n + 2) hβ u
  have hS : poleBranchSymmetricPoincareConstant hβ ≤ poleBranchSymmetricIntervalSup ha b :=
    le_csSup (poleBranchSymmetricIntervalValues_bddAbove ha hab) ⟨⟨β, hlo, hhi⟩, rfl⟩
  have hs' := hs.trans (mul_le_mul_of_nonneg_right hS (coulombFormEnergy_nonneg (n + 2) hβ u))
  have h := hlabel.trans (add_le_add hs'
    (le_rfl : paperCrelInterval a b * coulombFormEnergy (n + 2) hβ u ≤ _))
  simpa only [add_mul] using h

/-- The compact-interval coefficient is fixed before beta, N and the observable. -/
theorem paper_full_labeled_poincare_uniform {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < paperCAllInterval ha b ∧ ∀ β (hβ : 0 < β), a ≤ β → β ≤ b →
      ∀ (N : ℕ), 2 ≤ N → ∀ u : CoulombFormDomain N hβ,
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        paperCAllInterval ha b * coulombFormEnergy N hβ u :=
  ⟨paperCAllInterval_pos ha hab, fun _ hβ hlo hhi =>
    paper_full_labeled_poincare_compact ha hab hβ hlo hhi⟩

end RepulsiveCoulomb.PaperRoute
