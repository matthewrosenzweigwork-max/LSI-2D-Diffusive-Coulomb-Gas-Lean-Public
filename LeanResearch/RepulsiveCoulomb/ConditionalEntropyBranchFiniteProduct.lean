module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchBinaryKL
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
Literal finite-product coordinate charts, arbitrary-Q conditional kernels,
product reference correspondences, and projection of one-site conditional KL.
The coordinate removed at i is precisely Fin.succAbove i; no discrete-state
assumption or analytic tensorization theorem is used.
Records-only draft, not yet staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α : Type*} [MeasurableSpace α]

def conditionalEntropyBranchChart {n : ℕ} (i : Fin (n + 1)) :
    (Fin (n + 1) → α) ≃ᵐ (Fin n → α) × α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => α) i).trans MeasurableEquiv.prodComm

theorem conditionalEntropyBranchChart_apply {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → α) :
    conditionalEntropyBranchChart i x = ((fun j => x (i.succAbove j)), x i) := rfl

def conditionalEntropyBranchMarginal {n : ℕ} (Q : Measure (Fin (n + 1) → α))
    (i : Fin (n + 1)) : Measure (Fin n → α) :=
  (Q.map (conditionalEntropyBranchChart i)).fst

theorem conditionalEntropyBranchMarginal_eq_map {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) (i : Fin (n + 1)) :
    conditionalEntropyBranchMarginal Q i = Q.map (fun x j => x (i.succAbove j)) := by
  rw [conditionalEntropyBranchMarginal, Measure.fst,
    Measure.map_map measurable_fst (conditionalEntropyBranchChart i).measurable]
  rfl

instance conditionalEntropyBranchMarginal_isProbability {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q] (i : Fin (n + 1)) :
    IsProbabilityMeasure (conditionalEntropyBranchMarginal Q i) := by
  unfold conditionalEntropyBranchMarginal
  infer_instance

def conditionalEntropyBranchSiteCost {n : ℕ} (Q : Measure (Fin (n + 1) → α))
    (μ : Fin (n + 1) → Measure α) (i : Fin (n + 1)) : ℝ≥0∞ :=
  conditionalEntropyBranchCost (Q.map (conditionalEntropyBranchChart i)) (μ i)

/-- Actual product reference transformed by the exact coordinate chart. -/
theorem conditionalEntropyBranch_product_chart {n : ℕ}
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (n + 1)) :
    (Measure.pi μ).map (conditionalEntropyBranchChart i) =
      (Measure.pi (fun j => μ (i.succAbove j))).prod (μ i) := by
  exact ((Measure.measurePreserving_swap (μ := μ i)
    (ν := Measure.pi (fun j => μ (i.succAbove j)))).comp
      (measurePreserving_piFinSuccAbove μ i)).map_eq

/-- Each arbitrary-Q one-site kernel comes from standard-Borel disintegration
of the actual coordinate chart. -/
def conditionalEntropyBranchSiteKernel [StandardBorelSpace α] [Nonempty α] {n : ℕ}
    (Q : Measure (Fin (n + 1) → α)) [IsFiniteMeasure Q] (i : Fin (n + 1)) :
    Kernel (Fin n → α) α :=
  conditionalEntropyBranchKernel (Q.map (conditionalEntropyBranchChart i))

instance conditionalEntropyBranchSiteKernel_isMarkov [StandardBorelSpace α] [Nonempty α]
    {n : ℕ} (Q : Measure (Fin (n + 1) → α)) [IsFiniteMeasure Q] (i : Fin (n + 1)) :
    IsMarkovKernel (conditionalEntropyBranchSiteKernel Q i) := by
  unfold conditionalEntropyBranchSiteKernel
  infer_instance

theorem conditionalEntropyBranch_site_disintegration [StandardBorelSpace α] [Nonempty α]
    {n : ℕ} (Q : Measure (Fin (n + 1) → α)) [IsFiniteMeasure Q] (i : Fin (n + 1)) :
    conditionalEntropyBranchMarginal Q i ⊗ₘ conditionalEntropyBranchSiteKernel Q i =
      Q.map (conditionalEntropyBranchChart i) :=
  conditionalEntropyBranch_disintegration (Q.map (conditionalEntropyBranchChart i))

/-- The finite-product chain identity with all measures explicitly identified. -/
theorem conditionalEntropyBranch_site_chain [StandardBorelSpace α] [Nonempty α]
    {n : ℕ} (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1)) :
    klDiv Q (Measure.pi μ) =
      klDiv (conditionalEntropyBranchMarginal Q i) (Measure.pi (fun j => μ (i.succAbove j))) +
        conditionalEntropyBranchSiteCost Q μ i := by
  rw [← conditionalEntropyBranch_kl_map_equiv Q (Measure.pi μ)
    (conditionalEntropyBranchChart i), conditionalEntropyBranch_product_chart μ i]
  exact conditionalEntropyBranch_binary_chain (Q.map (conditionalEntropyBranchChart i))
    (Measure.pi (fun j => μ (i.succAbove j))) (μ i)

theorem conditionalEntropyBranch_site_finite [StandardBorelSpace α] [Nonempty α]
    {n : ℕ} (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hKL : klDiv Q (Measure.pi μ) ≠ ∞) (i : Fin (n + 1)) :
    klDiv (conditionalEntropyBranchMarginal Q i)
        (Measure.pi (fun j => μ (i.succAbove j))) ≠ ∞ ∧
      conditionalEntropyBranchSiteCost Q μ i ≠ ∞ := by
  rw [conditionalEntropyBranch_site_chain Q μ i] at hKL
  exact ENNReal.add_ne_top.mp hKL

def conditionalEntropyBranchTail {n : ℕ} (x : Fin (n + 1) → α) : Fin n → α :=
  fun j => x j.succ

theorem conditionalEntropyBranchTail_measurable (n : ℕ) :
    Measurable (conditionalEntropyBranchTail (α := α) (n := n)) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply j.succ)

/-- Deleting coordinate zero, then isolating i, is exactly isolating i+1,
then deleting coordinate zero from the outside vector. -/
theorem conditionalEntropyBranch_tail_chart {n : ℕ}
    (Q : Measure (Fin (n + 2) → α)) (i : Fin (n + 1)) :
    (Q.map conditionalEntropyBranchTail).map (conditionalEntropyBranchChart i) =
      (Q.map (conditionalEntropyBranchChart i.succ)).map
        (Prod.map conditionalEntropyBranchTail id) := by
  rw [Measure.map_map (conditionalEntropyBranchChart i).measurable
    (conditionalEntropyBranchTail_measurable (n + 1)),
    Measure.map_map ((conditionalEntropyBranchTail_measurable n).prodMap measurable_id)
      (conditionalEntropyBranchChart i.succ).measurable]
  congr 1
  funext x
  apply Prod.ext
  · funext j
    simp only [Function.comp_apply, conditionalEntropyBranchChart_apply,
      conditionalEntropyBranchTail, Prod.map_fst, Fin.succ_succAbove_succ]
  · rfl

/-- Literal finite-product conditioning monotonicity, supplying the inductive
step of continuous-product relative Han--Shearer. -/
theorem conditionalEntropyBranch_tail_cost_le {n : ℕ}
    (Q : Measure (Fin (n + 2) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 2) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (n + 1)) :
    conditionalEntropyBranchSiteCost (Q.map conditionalEntropyBranchTail) (fun j => μ j.succ) i ≤
      conditionalEntropyBranchSiteCost Q μ i.succ := by
  unfold conditionalEntropyBranchSiteCost
  rw [conditionalEntropyBranch_tail_chart Q i]
  exact conditionalEntropyBranch_cost_map_left
    (Q.map (conditionalEntropyBranchChart i.succ)) (μ i.succ)
      (conditionalEntropyBranchTail_measurable n)

theorem conditionalEntropyBranch_zero_chain [StandardBorelSpace α] [Nonempty α]
    {n : ℕ} (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
    (μ : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (μ i)] :
    klDiv Q (Measure.pi μ) =
      klDiv (Q.map conditionalEntropyBranchTail) (Measure.pi (fun j => μ j.succ)) +
        conditionalEntropyBranchSiteCost Q μ 0 := by
  change klDiv Q (Measure.pi μ) =
    klDiv (Q.map (fun (x : Fin (n + 1) → α) (j : Fin n) => x j.succ))
      (Measure.pi (fun (j : Fin n) => μ j.succ)) +
      conditionalEntropyBranchSiteCost Q μ 0
  simpa only [conditionalEntropyBranchMarginal_eq_map, Fin.zero_succAbove]
    using conditionalEntropyBranch_site_chain Q μ 0

end RepulsiveCoulomb
