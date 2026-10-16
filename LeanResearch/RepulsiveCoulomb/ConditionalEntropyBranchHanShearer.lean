module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchFiniteProduct
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Continuous finite-product relative Han--Shearer, proved by induction from the
actual arbitrary-law chain rule and the proved coordinate projection square.
The primary inequality is extended-valued and has no finiteness premise.
The subtractive manuscript identity is supplied only under finite global KL.
Records-only draft; not yet staged or checked.
-/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_probability_eq_subsingleton
    {δ : Type*} [MeasurableSpace δ] [Subsingleton δ]
    (P Q : Measure δ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : P = Q := by
  ext s hs
  by_cases h : s.Nonempty
  · obtain ⟨x, hx⟩ := h
    have hs' : s = Set.univ := Set.eq_univ_of_forall (fun y => by
      simpa only [Subsingleton.elim y x] using hx)
    simp only [hs', measure_univ]
  · have hs' : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp only [hs', measure_empty]

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- Extended-valued relative Han--Shearer for an actual continuous product.
Every site cost is the KL against the actual outside marginal times that
coordinate's reference probability. The conditional kernel is constructed in
ConditionalEntropyBranchFiniteProduct; none is assumed as a hypothesis. -/
theorem conditionalEntropyBranch_han_shearer (n : ℕ) :
    ∀ (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
      (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)],
      klDiv Q (Measure.pi μ) ≤ ∑ i, conditionalEntropyBranchSiteCost Q μ i := by
  induction n with
  | zero =>
      intro Q hQ μ hμ
      have heq : Q.map conditionalEntropyBranchTail =
          Measure.pi (fun j : Fin 0 => μ j.succ) :=
        conditionalEntropyBranch_probability_eq_subsingleton _ _
      rw [conditionalEntropyBranch_zero_chain Q μ, heq, klDiv_self, zero_add]
      simp
  | succ n ih =>
      intro Q hQ μ hμ
      have htail := ih (Q.map conditionalEntropyBranchTail) (fun j => μ j.succ)
      have hsum :
          (∑ i : Fin (n + 1), conditionalEntropyBranchSiteCost
            (Q.map conditionalEntropyBranchTail) (fun j => μ j.succ) i) ≤
          ∑ i : Fin (n + 1), conditionalEntropyBranchSiteCost Q μ i.succ := by
        exact Finset.sum_le_sum (fun i _ => conditionalEntropyBranch_tail_cost_le Q μ i)
      rw [conditionalEntropyBranch_zero_chain Q μ, Fin.sum_univ_succ]
      calc
        klDiv (Q.map conditionalEntropyBranchTail) (Measure.pi (fun j => μ j.succ)) +
            conditionalEntropyBranchSiteCost Q μ 0 ≤
          (∑ i : Fin (n + 1), conditionalEntropyBranchSiteCost Q μ i.succ) +
            conditionalEntropyBranchSiteCost Q μ 0 := add_le_add (htail.trans hsum) le_rfl
        _ = conditionalEntropyBranchSiteCost Q μ 0 +
            ∑ i : Fin (n + 1), conditionalEntropyBranchSiteCost Q μ i.succ := add_comm _ _

/-- All terms in the finite-real Han--Shearer statement are genuinely finite. -/
theorem conditionalEntropyBranch_sum_finite {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hKL : klDiv Q (Measure.pi μ) ≠ ∞) :
    (∑ i, conditionalEntropyBranchSiteCost Q μ i) ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  exact (conditionalEntropyBranch_site_finite Q μ hKL i).2

/-- Real-valued form of the inequality, converted only after proving the
whole conditional sum finite. -/
theorem conditionalEntropyBranch_han_shearer_real {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hKL : klDiv Q (Measure.pi μ) ≠ ∞) :
    (klDiv Q (Measure.pi μ)).toReal ≤
      ∑ i, (conditionalEntropyBranchSiteCost Q μ i).toReal := by
  have h := ENNReal.toReal_mono (conditionalEntropyBranch_sum_finite Q μ hKL)
    (conditionalEntropyBranch_han_shearer n Q μ)
  rw [ENNReal.toReal_sum (fun i _ => (conditionalEntropyBranch_site_finite Q μ hKL i).2)] at h
  exact h

/-- The equality printed in manuscript eq:han-shearer. No infinity-minus-
infinity operation appears: finite marginal and site terms are established
individually before converting and subtracting. -/
theorem conditionalEntropyBranch_han_shearer_identity {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hKL : klDiv Q (Measure.pi μ) ≠ ∞) :
    (∑ i, (conditionalEntropyBranchSiteCost Q μ i).toReal) =
      ((n + 1 : ℕ) : ℝ) * (klDiv Q (Measure.pi μ)).toReal -
        ∑ i, (klDiv (conditionalEntropyBranchMarginal Q i)
          (Measure.pi (fun j => μ (i.succAbove j)))).toReal := by
  have hi (i : Fin (n + 1)) :
      (conditionalEntropyBranchSiteCost Q μ i).toReal =
        (klDiv Q (Measure.pi μ)).toReal -
          (klDiv (conditionalEntropyBranchMarginal Q i)
            (Measure.pi (fun j => μ (i.succAbove j)))).toReal := by
    have h := congrArg ENNReal.toReal (conditionalEntropyBranch_site_chain Q μ i)
    obtain ⟨hm, hc⟩ := conditionalEntropyBranch_site_finite Q μ hKL i
    rw [ENNReal.toReal_add hm hc] at h
    linarith
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end RepulsiveCoulomb
