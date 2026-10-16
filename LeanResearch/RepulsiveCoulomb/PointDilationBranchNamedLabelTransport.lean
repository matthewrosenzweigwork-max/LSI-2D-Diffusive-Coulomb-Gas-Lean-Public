module

public import LeanResearch.RepulsiveCoulomb.PointDilationBranchNamedPairTransport
public import LeanResearch.RepulsiveCoulomb.CoulombPermutationGap

@[expose] public section

/-! RECORDS-ONLY UNCOMPILED. Sharp transposition and physical-gradient
summation cancel the particle factor, leaving the supplied P exactly. No
existential choice or max enlargement is used anywhere in the transport chain. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointDilationBranch_label_of_form_swap {β P : ℝ} (hβ : 0 < β) (hP : 0 < P)
    (hpair : ∀ (N : ℕ) (i j : Fin (N + 2)), i ≠ j →
      ∀ u : CoulombFormDomain (N + 2) hβ,
      ‖coulombFormSwapDifferenceL (N + 2) hβ i j u‖ ^ 2 ≤
        (2 * P) * ‖coulombFormPairGradientL (N + 2) hβ i j u‖ ^ 2) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
          P * coulombFormEnergy (N + 2) hβ u := by
  intro N u
  have ht := coulombValue_transposition_gap (N + 2) (by omega) hβ (coulombFormValueL (N + 2) hβ u)
  change 2 * ((N + 2 : ℕ) : ℝ) * ‖coulombFormValueL (N + 2) hβ u -
    coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
      ∑ p ∈ coulombPairs (N + 2), ‖coulombFormSwapDifferenceL (N + 2) hβ p.1 p.2 u‖ ^ 2 at ht
  have hs : (∑ p ∈ coulombPairs (N + 2), ‖coulombFormSwapDifferenceL (N + 2) hβ p.1 p.2 u‖ ^ 2) ≤
      (2 * P) * ∑ p ∈ coulombPairs (N + 2), ‖coulombFormPairGradientL (N + 2) hβ p.1 p.2 u‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact hpair N p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2) u
  have he := mul_le_mul_of_nonneg_left (coulombForm_pair_gradient_norm_sum_le N hβ u)
    (by positivity : 0 ≤ 2 * P)
  have hh := ht.trans (hs.trans he)
  have hpos : (0 : ℝ) < 2 * ((N + 2 : ℕ) : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  convert hh using 1 <;> ring

theorem pointDilationBranch_label_of_relative_core {β P : ℝ} (hβ : 0 < β) (hP : 0 < P)
    (hcore : ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
    variance (fun u : ℂ => φ (coulombRelativeInsert c u y)) (coulombRelativeKernel N β hβ (c, y)) ≤
      (P / 2) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y))) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
          P * coulombFormEnergy (N + 2) hβ u :=
  pointDilationBranch_label_of_form_swap hβ hP
    (pointDilationBranch_form_swap_of_core hβ
      (pointDilationBranch_all_pairs_swap_of_first hβ
        (pointDilationBranch_first_swap_of_relative hβ
          (pointDilationBranch_relative_swap_of_core hβ hcore))))

theorem pointDilationBranch_variance_reduction_of_label {β P : ℝ} (hβ : 0 < β)
    (hlabel : ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
          P * coulombFormEnergy (N + 2) hβ u) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) ≤
        variance (coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u) :
          CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) +
        P * coulombFormEnergy (N + 2) hβ u := by
  intro N u
  rw [coulombForm_variance_permutation_decomposition, coulombFormSymmetrizer_value]
  exact add_le_add le_rfl (hlabel N u)

end RepulsiveCoulomb
