module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchWeightedCost

@[expose] public section

/-! Two genuinely different factor spaces are allowed. Binary KL tensorization
is proved from the exact chain rule and marginal data processing, including
infinite entropy; no tensorization statement is taken as an assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace RepulsiveCoulomb

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Extended binary tensorization, stated before taking any real values. -/
theorem coulombCenter_binary_kl_tensorization [StandardBorelSpace B] [Nonempty B]
    (Q : Measure (A × B)) (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv Q (μ.prod ν) ≤
      klDiv Q (μ.prod Q.snd) + klDiv Q (Q.fst.prod ν) := by
  have hm : klDiv Q.fst μ ≤ klDiv Q (μ.prod Q.snd) := by
    have h := klDiv_map_le Q (μ.prod Q.snd) measurable_fst
    change klDiv Q.fst ((μ.prod Q.snd).map Prod.fst) ≤ _ at h
    rw [Measure.map_fst_prod, measure_univ, one_smul] at h
    exact h
  rw [conditionalEntropyBranch_binary_chain Q μ ν]
  unfold conditionalEntropyBranchCost
  exact add_le_add hm le_rfl

/-- Reverse conditional cost is literally the ordinary cost after swapping factors. -/
theorem coulombCenter_reverse_cost (Q : Measure (A × B))
    (μ : Measure A) [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] :
    klDiv Q (μ.prod Q.snd) =
      conditionalEntropyBranchCost (Q.map (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)) μ := by
  have h := conditionalEntropyBranch_kl_map_equiv Q (μ.prod Q.snd)
    (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
  have hs : (μ.prod Q.snd).map (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A) =
      Q.snd.prod μ := (Measure.measurePreserving_swap (μ := μ) (ν := Q.snd)).map_eq
  rw [hs] at h
  unfold conditionalEntropyBranchCost
  change klDiv Q (μ.prod Q.snd) = klDiv (Q.map Prod.swap) ((Q.map Prod.swap).fst.prod μ)
  rw [Measure.fst_map_swap]
  exact h.symm

/-- Product KL is finite whenever its two actual conditional costs are finite. -/
theorem coulombCenter_binary_kl_finite [StandardBorelSpace B] [Nonempty B]
    (Q : Measure (A × B)) (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : klDiv Q (μ.prod Q.snd) ≠ ∞) (hB : klDiv Q (Q.fst.prod ν) ≠ ∞) :
    klDiv Q (μ.prod ν) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
    (coulombCenter_binary_kl_tensorization Q μ ν)

theorem coulombCenter_binary_kl_tensorization_real [StandardBorelSpace B] [Nonempty B]
    (Q : Measure (A × B)) (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : klDiv Q (μ.prod Q.snd) ≠ ∞) (hB : klDiv Q (Q.fst.prod ν) ≠ ∞) :
    (klDiv Q (μ.prod ν)).toReal ≤
      (klDiv Q (μ.prod Q.snd)).toReal + (klDiv Q (Q.fst.prod ν)).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
    (coulombCenter_binary_kl_tensorization Q μ ν)
  rwa [ENNReal.toReal_add hA hB] at h

end RepulsiveCoulomb
