import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchCancellation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact even-moment expansion over ordered edge words, before support
counting. Loops are literally zeroed at the label level and each surviving
word is integrable by the independent absolute-diagram theorem. -/

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace RepulsiveCoulomb
variable {X : Type*} [MeasurableSpace X]

/-- The normalized ORDERED off-diagonal statistic. -/
def partitionMomentOrderedStatistic {N : ℕ} (G : X → X → ℝ) (x : Fin N → X) : ℝ :=
  (∑ ij : Fin N × Fin N, if ij.1 = ij.2 then 0 else G (x ij.1) (x ij.2)) / N

/-- A word containing a loop is exactly zero, not an evaluation of the kernel
on a spatial diagonal. Otherwise it is the original signed diagram. -/
def partitionMomentWord {N p : ℕ} (G : X → X → ℝ)
    (e : Fin p → Fin N × Fin N) (x : Fin N → X) : ℝ :=
  if ∀ j, (e j).1 ≠ (e j).2 then partitionMomentDiagram G e x else 0

theorem partitionMomentWord_eq_product {N p : ℕ}
    (G : X → X → ℝ) (e : Fin p → Fin N × Fin N) (x : Fin N → X) :
    partitionMomentWord G e x =
      ∏ j : Fin p, if (e j).1 = (e j).2 then 0 else G (x (e j).1) (x (e j).2) := by
  classical
  by_cases h : ∀ j, (e j).1 ≠ (e j).2
  · simp only [partitionMomentWord, if_pos h, partitionMomentDiagram]
    apply Finset.prod_congr rfl
    intro j _
    simp only [if_neg (h j)]
  · rw [partitionMomentWord, if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm

/-- Direct compatibility with an ordered off-diagonal double sum. -/
theorem partitionMomentOrderedStatistic_eq_nested_ite {N : ℕ}
    (G : X → X → ℝ) (x : Fin N → X) :
    partitionMomentOrderedStatistic G x =
      (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else G (x i) (x j)) / N := by
  simp only [partitionMomentOrderedStatistic, Fintype.sum_prod_type]

/-- This is the manuscript's sum over each label and all distinct second labels. -/
theorem partitionMomentOrderedStatistic_eq_nested {N : ℕ}
    (G : X → X → ℝ) (x : Fin N → X) :
    partitionMomentOrderedStatistic G x =
      (∑ i : Fin N, ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, G (x i) (x j)) / N := by
  unfold partitionMomentOrderedStatistic
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [if_true, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]

/-- Exact even absolute-power expansion, including all repeated and reversed
ordered edge occurrences with their correct multiplicities. -/
theorem partitionMomentOrderedStatistic_even_power {N p : ℕ}
    (G : X → X → ℝ) (hp : Even p) (x : Fin N → X) :
    |partitionMomentOrderedStatistic G x| ^ p =
      (1 / (N : ℝ)) ^ p * ∑ e : Fin p → Fin N × Fin N, partitionMomentWord G e x := by
  rw [hp.pow_abs, partitionMomentOrderedStatistic, div_pow, Fintype.sum_pow]
  simp_rw [← partitionMomentWord_eq_product]
  simp only [one_div, inv_pow, div_eq_mul_inv] <;> ring

theorem partitionMomentWord_integrable {N p : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x) (hp : 0 < p)
    (B : ℝ) (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ B)
    (e : Fin p → Fin N × Fin N) :
    Integrable (partitionMomentWord G e) (Measure.pi (fun _ : Fin N => μ)) := by
  classical
  change Integrable (fun x : Fin N → X =>
    if ∀ j, (e j).1 ≠ (e j).2 then partitionMomentDiagram G e x else 0)
    (Measure.pi (fun _ : Fin N => μ))
  by_cases h : ∀ j, (e j).1 ≠ (e j).2
  · simp only [if_pos h]
    exact partitionMomentDiagram_integrable G hG hsymm e h hp B hrowInt hrow
  · simp only [if_neg h]
    exact integrable_zero _ _ _

/-- Integrability of the actual p-th statistic moment is proved from all
absolute diagram integrals before integrating the signed expansion. -/
theorem partitionMomentOrderedStatistic_moment_integrable {N p : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x) (hp : 0 < p) (heven : Even p)
    (B : ℝ) (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ B) :
    Integrable (fun x : Fin N → X => |partitionMomentOrderedStatistic G x| ^ p)
      (Measure.pi (fun _ : Fin N => μ)) := by
  have h := (integrable_finsetSum (Finset.univ : Finset (Fin p → Fin N × Fin N))
    (fun e _ => partitionMomentWord_integrable G hG hsymm hp B hrowInt hrow e)).const_mul
      ((1 / (N : ℝ)) ^ p)
  simpa only [partitionMomentOrderedStatistic_even_power G heven] using h

/-- The integrated expansion uses justified finite linearity. -/
theorem partitionMomentOrderedStatistic_moment_eq_sum {N p : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x) (hp : 0 < p) (heven : Even p)
    (B : ℝ) (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ B) :
    (∫ x : Fin N → X, |partitionMomentOrderedStatistic G x| ^ p
      ∂Measure.pi (fun _ : Fin N => μ)) =
      (1 / (N : ℝ)) ^ p * ∑ e : Fin p → Fin N × Fin N,
        ∫ x, partitionMomentWord G e x ∂Measure.pi (fun _ : Fin N => μ) := by
  simp_rw [partitionMomentOrderedStatistic_even_power G heven]
  rw [integral_const_mul, integral_finsetSum]
  intro e _
  exact partitionMomentWord_integrable G hG hsymm hp B hrowInt hrow e

end RepulsiveCoulomb
