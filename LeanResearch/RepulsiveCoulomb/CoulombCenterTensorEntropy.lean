module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterTensorKL
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchTransport

@[expose] public section

/-! Actual heterogeneous product entropy estimate from the two slice estimates.
The conditional costs, their finiteness and the density disintegrations are
constructed, rather than assumed. This is the core tensorization step. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The conditional cost of a product-density law is controlled by the actual
slice entropies, with zero-mass fibers and finite-real passage justified. -/
theorem coulombCenter_product_cost_upper [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hFi : ∀ a, Integrable (fun b => F (a, b)) ν)
    (hFl : ∀ a, Integrable (fun b => F (a, b) * Real.log (F (a, b))) ν)
    (hF : Integrable F (μ.prod ν)) (hmass : (∫ p, F p ∂μ.prod ν) = 1)
    {E : A → ℝ} (hE : Integrable E μ) (C : ℝ)
    (hbound : ∀ a, entropy ν (fun b => F (a, b)) ≤ ((C * E a : ℝ) : EReal)) :
    conditionalEntropyBranchCost (conditionalEntropyBranchDensityLaw (μ.prod ν) F) ν ≠ ∞ ∧
      (conditionalEntropyBranchCost (conditionalEntropyBranchDensityLaw (μ.prod ν) F) ν).toReal ≤
        C * (∫ a, E a ∂μ) := by
  letI : IsProbabilityMeasure (conditionalEntropyBranchDensityLaw (μ.prod ν) F) :=
    conditionalEntropyBranchDensityLaw_probability hF0 hF hmass
  let κ : Kernel A B := Kernel.const A ν
  have hF' : Integrable F (μ ⊗ₘ κ) := by
    simpa only [κ, Measure.compProd_const] using hF
  have hm' : (∫ p, F p ∂μ ⊗ₘ κ) = 1 := by
    simpa only [κ, Measure.compProd_const] using hmass
  have hcost := conditionalEntropyBranch_integrated_cost_upper μ κ
    hFm hF0 hFi hFl hF' hm' hE C hbound
  have hMarg := conditionalEntropyBranch_density_marginal μ κ
    hFm hF0 hFi hF' hm'
  rw [← hMarg] at hcost
  simpa only [κ, Measure.compProd_const, conditionalEntropyBranchCost] using hcost

/-- Normalized product entropy is bounded by the sum of actual factor
energies, with precisely the common slice coefficient C. -/
theorem coulombCenter_normalized_tensor_entropy
    [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hFAi : ∀ b, Integrable (fun a => F (a, b)) μ)
    (hFAl : ∀ b, Integrable (fun a => F (a, b) * Real.log (F (a, b))) μ)
    (hFBi : ∀ a, Integrable (fun b => F (a, b)) ν)
    (hFBl : ∀ a, Integrable (fun b => F (a, b) * Real.log (F (a, b))) ν)
    (hF : Integrable F (μ.prod ν)) (hmass : (∫ p, F p ∂μ.prod ν) = 1)
    {EA : B → ℝ} {EB : A → ℝ} (hEA : Integrable EA ν) (hEB : Integrable EB μ) (C : ℝ)
    (hboundA : ∀ b, entropy μ (fun a => F (a, b)) ≤ ((C * EA b : ℝ) : EReal))
    (hboundB : ∀ a, entropy ν (fun b => F (a, b)) ≤ ((C * EB a : ℝ) : EReal)) :
    entropy (μ.prod ν) F ≤ ((C * ((∫ b, EA b ∂ν) + ∫ a, EB a ∂μ) : ℝ) : EReal) := by
  let Q := conditionalEntropyBranchDensityLaw (μ.prod ν) F
  letI : IsProbabilityMeasure Q := conditionalEntropyBranchDensityLaw_probability hF0 hF hmass
  have hB := coulombCenter_product_cost_upper μ ν hFm hF0 hFBi hFBl hF hmass hEB C hboundB
  let Fs : B × A → ℝ := fun p => F (p.2, p.1)
  have hsm : Measurable Fs := hFm.comp measurable_swap
  have hs0 : ∀ p, 0 ≤ Fs p := fun p => hF0 (p.2, p.1)
  have hsi : Integrable Fs (ν.prod μ) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).integrable_comp_of_integrable hF
  have hsmass : (∫ p, Fs p ∂ν.prod μ) = 1 :=
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).integral_comp
      (MeasurableEquiv.prodComm : B × A ≃ᵐ A × B).measurableEmbedding F).trans hmass
  have hA := coulombCenter_product_cost_upper ν μ hsm hs0 hFAi hFAl hsi hsmass hEA C hboundA
  have hsLaw : Q.map (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A) =
      conditionalEntropyBranchDensityLaw (ν.prod μ) Fs := by
    dsimp only [Q]
    rw [conditionalEntropyBranch_densityLaw_map _ _ hFm]
    change conditionalEntropyBranchDensityLaw ((μ.prod ν).map Prod.swap) Fs = _
    rw [(Measure.measurePreserving_swap (μ := μ) (ν := ν)).map_eq]
  have hrev := coulombCenter_reverse_cost Q μ
  rw [hsLaw] at hrev
  rw [← hrev] at hA
  have hfin := coulombCenter_binary_kl_finite Q μ ν hA.1 hB.1
  have ht := coulombCenter_binary_kl_tensorization_real Q μ ν hA.1 hB.1
  rw [conditionalEntropyBranch_normalized_entropy_kl hFm hF0 hF hmass,
    ← EReal.coe_ennreal_toReal hfin]
  apply EReal.coe_le_coe_iff.mpr
  calc
    (klDiv Q (μ.prod ν)).toReal ≤
        (klDiv Q (μ.prod Q.snd)).toReal + (klDiv Q (Q.fst.prod ν)).toReal := ht
    _ ≤ C * (∫ b, EA b ∂ν) + C * (∫ a, EB a ∂μ) := add_le_add hA.2 hB.2
    _ = C * ((∫ b, EA b ∂ν) + ∫ a, EB a ∂μ) := by ring

end RepulsiveCoulomb
