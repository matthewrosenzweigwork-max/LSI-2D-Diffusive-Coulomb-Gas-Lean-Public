module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCompleteFactorization

@[expose] public section

/-!
The literal supremum defect over every particle number at least two. Genuine
boundedness is proved before using real sSup, preventing a default-value
substitute for an infinite supremum. Records-only, wholly uncompiled closure.
-/
noncomputable section
open MeasureTheory InformationTheory Real Set
open scoped ENNReal
namespace RepulsiveCoulomb

def conditionalEntropyBranchUniformDefect {β : ℝ}
    (R : EquilibriumConstructedReference β) (ell : ℝ) : ℝ :=
  sSup (Set.range (fun n : ℕ => conditionalEntropyBranchDefect (N := n + 2) R ell))

theorem conditionalEntropyBranch_defect_range_bddAbove {β ell : ℝ}
    (hβ : 0 < β) (hell : 1 < ell) (R : EquilibriumConstructedReference β) :
    BddAbove (Set.range (fun n : ℕ => conditionalEntropyBranchDefect (N := n + 2) R ell)) := by
  obtain ⟨D, hD, hb⟩ := conditionalEntropyBranch_defect_compact_upper hβ le_rfl hell
  refine ⟨D, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact hb β le_rfl le_rfl R (n + 2) (by omega)

theorem conditionalEntropyBranch_defect_le_uniform {N : ℕ} {β ell : ℝ}
    (hN : 2 ≤ N) (hβ : 0 < β) (hell : 1 < ell) (R : EquilibriumConstructedReference β) :
    conditionalEntropyBranchDefect (N := N) R ell ≤ conditionalEntropyBranchUniformDefect R ell := by
  apply le_csSup (conditionalEntropyBranch_defect_range_bddAbove hβ hell R)
  refine ⟨N - 2, ?_⟩
  change conditionalEntropyBranchDefect (N := N - 2 + 2) R ell =
    conditionalEntropyBranchDefect (N := N) R ell
  rw [Nat.sub_add_cancel hN]

theorem conditionalEntropyBranch_uniform_defect_nonneg {β ell : ℝ}
    (hβ : 0 < β) (hell : 1 < ell) (R : EquilibriumConstructedReference β) :
    0 ≤ conditionalEntropyBranchUniformDefect R ell :=
  (conditionalEntropyBranch_defect_nonneg (N := 2) (by norm_num) hβ hell R).trans
    (conditionalEntropyBranch_defect_le_uniform (N := 2) le_rfl hβ hell R)

theorem conditionalEntropyBranch_uniform_defect_compact {βlo βhi ell : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hell : 1 < ell) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi)
      (R : EquilibriumConstructedReference β), conditionalEntropyBranchUniformDefect R ell ≤ D := by
  obtain ⟨D, hD, hb⟩ := conditionalEntropyBranch_defect_compact_upper hlo hord hell
  refine ⟨D, hD, ?_⟩
  intro β hβlo hβhi R
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact hb β hβlo hβhi R (n + 2) (by omega)

theorem conditionalEntropyBranch_uniform_factorization {N : ℕ} {β : ℝ}
    (hN : 2 ≤ N + 1) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q)
    {ell : ℝ} (hell : 1 < ell) :
    (1 - 1 / ell) * (klDiv Q (coulombMeasure (N + 1) β)).toReal -
      conditionalEntropyBranchUniformDefect R ell ≤
        (conditionalEntropyBranchCoulombS hβ Q).toReal := by
  have h := conditionalEntropyBranch_factorization_defect_of_exp_integrable hβ R hKL hB hell
    (conditionalEntropyBranch_defect_exp_integrable (Nat.succ_pos N) hβ (zero_lt_one.trans hell) R)
  exact (sub_le_sub_left (conditionalEntropyBranch_defect_le_uniform hN hβ hell R) _).trans h

end RepulsiveCoulomb
