module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalInputLabeledLSI
public import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalLSIInfimum

@[expose] public section

/-! The exact actual-optimal-rate packaging of the new original-input LSI.
The frozen optimum is the supremum of rates admissible on the original full
physical form, and both infima are the genuine order-theoretic infima. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb.PaperRoute

theorem paperOriginalLabeledRate_le_optimal {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) :
    paperOriginalLabeledRate hβ ≤ poleBranchOptimalLSIRate N hβ :=
  poleBranch_admissible_le_optimalLSIRate hN hβ
    ⟨paperOriginalLabeledRate_pos hβ, paper_full_labeled_lsi_original hβ N hN⟩

theorem paperOriginalLabeledRate_le_particle_inf {β : ℝ} (hβ : 0 < β) :
    paperOriginalLabeledRate hβ ≤ poleBranchOptimalLSIParticleRealInf hβ := by
  apply le_csInf (poleBranchOptimalLSIParticleValues_nonempty hβ)
  rintro r ⟨N, rfl⟩
  exact paperOriginalLabeledRate_le_optimal hβ N N.2

theorem paper_original_particle_optimal_inf_pos {β : ℝ} (hβ : 0 < β) :
    0 < poleBranchOptimalLSIParticleRealInf hβ :=
  (paperOriginalLabeledRate_pos hβ).trans_le (paperOriginalLabeledRate_le_particle_inf hβ)

theorem paperOriginalCompactLabeledRate_le_optimal {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (β : Set.Icc a b) (N : ℕ) (hN : 2 ≤ N) :
    paperOriginalCompactLabeledRate (b := b) ha ≤
      poleBranchOptimalLSIRate N (ha.trans_le β.2.1) :=
  poleBranch_admissible_le_optimalLSIRate hN (ha.trans_le β.2.1)
    ⟨paperOriginalCompactLabeledRate_pos ha hab,
      (paper_uniform_labeled_lsi_original ha hab).2 β N hN⟩

theorem paper_original_compact_optimal_double_inf_lower {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (paperOriginalCompactLabeledRate (b := b) ha : EReal) ≤
      poleBranchOptimalLSIInfOn (Set.Icc a b) (fun _ hβ => ha.trans_le hβ.1) := by
  apply poleBranchOptimalLSIInfOn_ge_common_rate _ _
    (paperOriginalCompactLabeledRate_pos ha hab)
  intro β hβ N hN u
  exact (paper_uniform_labeled_lsi_original ha hab).2 ⟨β, hβ⟩ N hN u

theorem paper_original_compact_optimal_real_double_inf_lower {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    paperOriginalCompactLabeledRate (b := b) ha ≤
      poleBranchOptimalLSIRealInfOn (Set.Icc a b) (fun _ hβ => ha.trans_le hβ.1) := by
  have h := paper_original_compact_optimal_double_inf_lower ha hab
  rw [poleBranchOptimalLSIInfOn_eq_real (Set.Icc a b)
    (fun _ hβ => ha.trans_le hβ.1) (show (Set.Icc a b).Nonempty from ⟨a, le_rfl, hab⟩)] at h
  exact_mod_cast h

theorem paper_original_compact_optimal_double_inf_pos {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    0 < poleBranchOptimalLSIInfOn (Set.Icc a b) (fun _ hβ => ha.trans_le hβ.1) ∧
    0 < poleBranchOptimalLSIRealInfOn (Set.Icc a b) (fun _ hβ => ha.trans_le hβ.1) := by
  refine ⟨?_, (paperOriginalCompactLabeledRate_pos ha hab).trans_le
    (paper_original_compact_optimal_real_double_inf_lower ha hab)⟩
  exact (by exact_mod_cast paperOriginalCompactLabeledRate_pos ha hab :
    (0 : EReal) < (paperOriginalCompactLabeledRate (b := b) ha : EReal)).trans_le
    (paper_original_compact_optimal_double_inf_lower ha hab)

end RepulsiveCoulomb.PaperRoute
