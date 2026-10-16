module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

@[expose] public section

/-!
Actual arbitrary-law disintegration and extended-valued product KL chain rules.
The conditional law below is the pinned standard-Borel construction, not a
Gibbs conditional kernel supplied as an analytic assumption. In particular,
the identities hold when either side is infinite and never subtract infinities.

Pinned library attribution is retained in the imported Mathlib files (Rémy
Degenne and Lorenzo Luccioli for KL; the disintegration source for its authors).
Records-only draft: this file has not been checked or authorized for staging.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ]

/-- KL is invariant under a genuine measurable equivalence, including infinity. -/
theorem conditionalEntropyBranch_kl_map_equiv (Q P : Measure α)
    [IsFiniteMeasure Q] [IsFiniteMeasure P] (e : α ≃ᵐ β) :
    klDiv (Q.map e) (P.map e) = klDiv Q P := by
  apply le_antisymm
  · exact klDiv_map_le Q P e.measurable
  · have h := klDiv_map_le (Q.map e) (P.map e) e.symm.measurable
    simpa only [MeasurableEquiv.map_symm_map] using h

/-- The arbitrary competitor's conditional law is genuinely constructed. -/
def conditionalEntropyBranchKernel [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) [IsFiniteMeasure Q] : Kernel α β := Q.condKernel

instance conditionalEntropyBranchKernel_isMarkov [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) [IsFiniteMeasure Q] :
    IsMarkovKernel (conditionalEntropyBranchKernel Q) := by
  unfold conditionalEntropyBranchKernel
  infer_instance

theorem conditionalEntropyBranch_disintegration [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) [IsFiniteMeasure Q] :
    Q.fst ⊗ₘ conditionalEntropyBranchKernel Q = Q :=
  Q.disintegrate Q.condKernel

/-- Conditional divergence relative to a product reference, as a joint KL.
Its later identification with the integral of fiber KL is a separate theorem. -/
def conditionalEntropyBranchCost (Q : Measure (α × β)) (ν : Measure β) : ℝ≥0∞ :=
  klDiv Q (Q.fst.prod ν)

/-- Genuine continuous-space binary chain rule. No entropy finiteness is used. -/
theorem conditionalEntropyBranch_binary_chain [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure Q] [IsFiniteMeasure μ] [IsProbabilityMeasure ν] :
    klDiv Q (μ.prod ν) = klDiv Q.fst μ + conditionalEntropyBranchCost Q ν := by
  have h := klDiv_compProd_eq_add Q.fst μ (conditionalEntropyBranchKernel Q)
    (Kernel.const α ν)
  simpa only [conditionalEntropyBranch_disintegration, Measure.compProd_const,
    conditionalEntropyBranchCost] using h

theorem conditionalEntropyBranch_cost_le_full [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure Q] [IsFiniteMeasure μ] [IsProbabilityMeasure ν] :
    conditionalEntropyBranchCost Q ν ≤ klDiv Q (μ.prod ν) := by
  rw [conditionalEntropyBranch_binary_chain Q μ ν]
  exact le_add_left le_rfl

/-- Finite full entropy implies finite marginal and conditional terms. This is
recorded before taking real values or rearranging the chain identity. -/
theorem conditionalEntropyBranch_binary_finite [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure Q] [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (h : klDiv Q (μ.prod ν) ≠ ∞) :
    klDiv Q.fst μ ≠ ∞ ∧ conditionalEntropyBranchCost Q ν ≠ ∞ := by
  rw [conditionalEntropyBranch_binary_chain Q μ ν] at h
  exact ENNReal.add_ne_top.mp h

/-- The finite real chain is derived from the extended-valued one only after
both summands have been proved finite. -/
theorem conditionalEntropyBranch_binary_chain_real [StandardBorelSpace β] [Nonempty β]
    (Q : Measure (α × β)) (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure Q] [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (h : klDiv Q (μ.prod ν) ≠ ∞) :
    (klDiv Q (μ.prod ν)).toReal = (klDiv Q.fst μ).toReal +
      (conditionalEntropyBranchCost Q ν).toReal := by
  obtain ⟨hm, hc⟩ := conditionalEntropyBranch_binary_finite Q μ ν h
  rw [conditionalEntropyBranch_binary_chain Q μ ν, ENNReal.toReal_add hm hc]

/-- Dropping some of the conditioning coordinates can only decrease the
conditional divergence. The actual projected comparison measure is proved
using product-map and marginal-map identities, rather than postulated. -/
theorem conditionalEntropyBranch_cost_map_left (Q : Measure (α × β))
    (ν : Measure β) [IsFiniteMeasure Q] [IsProbabilityMeasure ν]
    {f : α → γ} (hf : Measurable f) :
    conditionalEntropyBranchCost (Q.map (Prod.map f id)) ν ≤
      conditionalEntropyBranchCost Q ν := by
  have hfst : (Q.map (Prod.map f id)).fst = Q.fst.map f := by
    simp only [Measure.fst, Measure.map_map measurable_fst (hf.prodMap measurable_id),
      Measure.map_map hf measurable_fst]
    rfl
  have hprod : (Q.fst.prod ν).map (Prod.map f id) = (Q.fst.map f).prod ν := by
    rw [← Measure.map_prod_map Q.fst ν hf measurable_id, Measure.map_id]
  have h := klDiv_map_le Q (Q.fst.prod ν) (hf.prodMap measurable_id)
  simpa only [conditionalEntropyBranchCost, hfst, hprod] using h

end RepulsiveCoulomb
