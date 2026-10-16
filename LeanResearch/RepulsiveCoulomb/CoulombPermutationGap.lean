import LeanResearch.RepulsiveCoulomb.HilbertTranspositionGap
import LeanResearch.RepulsiveCoulomb.CoulombFormSymmetrizer
import LeanResearch.RepulsiveCoulomb.CoulombFormPairSum

/-! Actual Gibbs L2 transposition gap and full-domain label-dependent variance bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

theorem coulombValue_transposition_gap (N : ℕ) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    2 * (N : ℝ) * ‖v - coulombSymmetrizer N hβ v‖ ^ 2 ≤
      ∑ p ∈ coulombPairs N, ‖v - coulombValuePermuteL N hβ (Equiv.swap p.1 p.2) v‖ ^ 2 :=
  hilbert_transposition_gap_pairs hN (coulombValueRepresentation N hβ)
    (coulombValueRepresentation_inner N hβ) v

theorem coulombForm_label_dependent_bound {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
          P * coulombFormEnergy (N + 2) hβ u := by
  obtain ⟨P,hP,hpair⟩ := coulombForm_all_pairs_swap_norm hβ
  refine ⟨P,hP,?_⟩
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

theorem coulombForm_label_dependent_bound_form {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u)‖ ^ 2 ≤
          P * coulombFormEnergy (N + 2) hβ u := by
  simpa only [coulombFormSymmetrizer_value] using coulombForm_label_dependent_bound hβ

theorem coulombForm_variance_reduction_to_symmetric {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) ≤
        variance (coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u) :
          CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) +
        P * coulombFormEnergy (N + 2) hβ u := by
  obtain ⟨P,hP,h⟩ := coulombForm_label_dependent_bound_form hβ
  refine ⟨P,hP,?_⟩
  intro N u
  rw [coulombForm_variance_permutation_decomposition]
  linarith [h N u]

end RepulsiveCoulomb
