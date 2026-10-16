module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchHanShearer
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchKernelIntegral

@[expose] public section

/-!
Literal expected one-site conditional divergences and manuscript eq:han-shearer.
Every arbitrary competitor conditional is the constructed standard-Borel law,
with proved measurability and finite-real integration where required.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

theorem conditionalEntropyBranch_site_kl_measurable {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1)) :
    Measurable (fun y => klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)) := by
  simpa only [Kernel.const_apply] using conditionalEntropyBranch_fiber_kl_measurable
    (conditionalEntropyBranchSiteKernel Q i) (Kernel.const (Fin n → α) (μ i))

theorem conditionalEntropyBranch_site_cost_integral {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1)) :
    conditionalEntropyBranchSiteCost Q μ i =
      ∫⁻ y, klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)
        ∂conditionalEntropyBranchMarginal Q i :=
  conditionalEntropyBranch_cost_eq_integral (Q.map (conditionalEntropyBranchChart i)) (μ i)

/-- Extended-valued expected-conditional form, valid without finite entropy. -/
theorem conditionalEntropyBranch_han_integral {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] :
    klDiv Q (Measure.pi μ) ≤
      ∑ i, ∫⁻ y, klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)
        ∂conditionalEntropyBranchMarginal Q i := by
  simpa only [conditionalEntropyBranch_site_cost_integral Q μ] using
    conditionalEntropyBranch_han_shearer n Q μ

theorem conditionalEntropyBranch_site_cost_integral_real {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hKL : klDiv Q (Measure.pi μ) ≠ ∞) (i : Fin (n + 1)) :
    (conditionalEntropyBranchSiteCost Q μ i).toReal =
      ∫ y, (klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)).toReal
        ∂conditionalEntropyBranchMarginal Q i := by
  have hm := conditionalEntropyBranch_site_kl_measurable Q μ i
  have hf : (∫⁻ y, klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)
      ∂conditionalEntropyBranchMarginal Q i) ≠ ∞ := by
    rw [← conditionalEntropyBranch_site_cost_integral Q μ i]
    exact (conditionalEntropyBranch_site_finite Q μ hKL i).2
  rw [conditionalEntropyBranch_site_cost_integral Q μ i]
  exact (integral_toReal hm.aemeasurable (ae_lt_top hm hf)).symm

/-- Both the equality and inequality of manuscript eq:han-shearer, for every
finite-entropy competitor on the continuous finite product. -/
theorem conditionalEntropyBranch_han_integral_real {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hKL : klDiv Q (Measure.pi μ) ≠ ∞) :
    (∑ i, ∫ y, (klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)).toReal
        ∂conditionalEntropyBranchMarginal Q i) =
      ((n + 1 : ℕ) : ℝ) * (klDiv Q (Measure.pi μ)).toReal -
        ∑ i, (klDiv (conditionalEntropyBranchMarginal Q i)
          (Measure.pi (fun j => μ (i.succAbove j)))).toReal ∧
    (klDiv Q (Measure.pi μ)).toReal ≤
      ∑ i, ∫ y, (klDiv (conditionalEntropyBranchSiteKernel Q i y) (μ i)).toReal
        ∂conditionalEntropyBranchMarginal Q i := by
  constructor
  · simpa only [conditionalEntropyBranch_site_cost_integral_real Q μ hKL] using
      conditionalEntropyBranch_han_shearer_identity Q μ hKL
  · simpa only [conditionalEntropyBranch_site_cost_integral_real Q μ hKL] using
      conditionalEntropyBranch_han_shearer_real Q μ hKL

end RepulsiveCoulomb
