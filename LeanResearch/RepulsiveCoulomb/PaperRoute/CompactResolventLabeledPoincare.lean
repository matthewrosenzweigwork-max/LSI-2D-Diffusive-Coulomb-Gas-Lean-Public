module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ResolventLabeledPoincare

@[expose] public section

/-! Additive compact-temperature application of the freshly proved
resolvent-fed symmetric endpoint. No new constants and no coefficient change. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb.PaperRoute

/-- Literal compact-temperature full-domain bound, with one fixed cap 2*b. -/
theorem paper_full_labeled_poincare_compact_via_resolvent {a b β : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (poleBranchSymmetricIntervalSup ha b + paperCrelInterval a b) * coulombFormEnergy N hβ u := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hlabel := paper_variance_reduction_interval ha hβ hlo hhi n u
  rw [coulombFormSymmetrizer_value] at hlabel
  have hs := paper_symmetrized_poincare_via_resolvent (by omega : 2 ≤ n + 2) hβ u
  have hS : poleBranchSymmetricPoincareConstant hβ ≤ poleBranchSymmetricIntervalSup ha b :=
    le_csSup (poleBranchSymmetricIntervalValues_bddAbove ha hab) ⟨⟨β, hlo, hhi⟩, rfl⟩
  have hs' := hs.trans (mul_le_mul_of_nonneg_right hS (coulombFormEnergy_nonneg (n + 2) hβ u))
  have h := hlabel.trans (add_le_add hs'
    (le_rfl : paperCrelInterval a b * coulombFormEnergy (n + 2) hβ u ≤ _))
  simpa only [add_mul] using h

/-- The compact-interval coefficient is fixed before beta, N and the observable. -/
theorem paper_full_labeled_poincare_uniform_via_resolvent {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < paperCAllInterval ha b ∧ ∀ β (hβ : 0 < β), a ≤ β → β ≤ b →
      ∀ (N : ℕ), 2 ≤ N → ∀ u : CoulombFormDomain N hβ,
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        paperCAllInterval ha b * coulombFormEnergy N hβ u :=
  ⟨paperCAllInterval_pos ha hab, fun _ hβ hlo hhi =>
    paper_full_labeled_poincare_compact_via_resolvent ha hab hβ hlo hhi⟩

end RepulsiveCoulomb.PaperRoute
