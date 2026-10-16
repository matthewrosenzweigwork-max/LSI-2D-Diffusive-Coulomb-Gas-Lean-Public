import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchDensityDisintegration
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchKernelIntegral

/-!
Outer-marginal weighting of actual conditional KL and its integral upper bound
from the literal extended one-site entropy. Zero-mass fibers are normalized
measurably and carry zero weight. All uses of real-valued KL are accompanied
by pointwise and integrated finiteness proofs. Records-only, unchecked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
  {F : α × β → ℝ}

theorem conditionalEntropyBranch_outer_integrable_iff (hFm : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) (g : α → ℝ) :
    Integrable g (conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F)) ↔
      Integrable (fun a => conditionalEntropyBranchFiberMass κ F a * g a) μ := by
  have hmass0 (a : α) : 0 ≤ conditionalEntropyBranchFiberMass κ F a :=
    integral_nonneg (fun b => hF0 (a, b))
  simpa only [conditionalEntropyBranchDensityLaw, ENNReal.toReal_ofReal (hmass0 _), mul_comm] using
    (integrable_withDensity_iff (conditionalEntropyBranchFiberMass_measurable κ hFm).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := g))

theorem conditionalEntropyBranch_outer_integral (hFm : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) (g : α → ℝ) :
    (∫ a, g a ∂conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F)) =
      ∫ a, conditionalEntropyBranchFiberMass κ F a * g a ∂μ := by
  have hmass0 (a : α) : 0 ≤ conditionalEntropyBranchFiberMass κ F a :=
    integral_nonneg (fun b => hF0 (a, b))
  simpa only [conditionalEntropyBranchDensityLaw, ENNReal.toReal_ofReal (hmass0 _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul
      (conditionalEntropyBranchFiberMass_measurable κ hFm).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g)

/-- Integrating an actual one-site entropy upper bound gives a conditional-KL
upper bound for the density law. The displayed comparison law uses the proved
outside marginal, and the conditional law is the explicit normalized kernel.
The theorem does not assume that the competitor already has finite global KL.
-/
theorem conditionalEntropyBranch_integrated_cost_upper [StandardBorelSpace β] [Nonempty β]
    (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hFi : ∀ a, Integrable (fun b => F (a, b)) (κ a))
    (hFl : ∀ a, Integrable (fun b => F (a, b) * Real.log (F (a, b))) (κ a))
    (hF : Integrable F (μ ⊗ₘ κ)) (hmass : (∫ p, F p ∂μ ⊗ₘ κ) = 1)
    {E : α → ℝ} (hE : Integrable E μ) (C : ℝ)
    (hbound : ∀ a, entropy (κ a) (fun b => F (a, b)) ≤ ((C * E a : ℝ) : EReal)) :
    klDiv (conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F)
        (conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F) ⊗ₘ κ) ≠ ∞ ∧
      (klDiv (conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F)
        (conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F) ⊗ₘ κ)).toReal ≤
        C * (∫ a, E a ∂μ) := by
  let η := conditionalEntropyBranchNormalizedKernel κ hFm
  let R := conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F)
  letI : IsMarkovKernel η := conditionalEntropyBranchNormalizedKernel_isMarkov κ hFm hF0 hFi
  letI : IsProbabilityMeasure R := conditionalEntropyBranch_outer_density_probability μ κ hF0 hF hmass
  have hfinite (a : α) : klDiv (η a) (κ a) ≠ ∞ := by
    have h := (conditionalEntropyBranch_density_entropy (F := fun b => F (a, b))
      (hFm.comp measurable_prodMk_left)
      (fun b => hF0 (a, b)) (hFi a) (hFl a)).1
    simpa only [η, conditionalEntropyBranchNormalizedKernel_apply] using h
  have hent (a : α) : entropy (κ a) (fun b => F (a, b)) =
      ((conditionalEntropyBranchFiberMass κ F a * (klDiv (η a) (κ a)).toReal : ℝ) : EReal) := by
    simpa only [η, conditionalEntropyBranchNormalizedKernel_apply, conditionalEntropyBranchFiberMass]
      using (conditionalEntropyBranch_density_entropy (F := fun b => F (a, b))
      (hFm.comp measurable_prodMk_left)
        (fun b => hF0 (a, b)) (hFi a) (hFl a)).2
  have hk := conditionalEntropyBranch_fiber_kl_measurable η κ
  have hmass0 (a : α) : 0 ≤ conditionalEntropyBranchFiberMass κ F a :=
    integral_nonneg (fun b => hF0 (a, b))
  have hmg (a : α) : conditionalEntropyBranchFiberMass κ F a * (klDiv (η a) (κ a)).toReal ≤ C * E a := by
    have h := hbound a
    rw [hent a] at h
    exact EReal.coe_le_coe_iff.mp h
  have hmgi : Integrable
      (fun a => conditionalEntropyBranchFiberMass κ F a * (klDiv (η a) (κ a)).toReal) μ := by
    apply (hE.const_mul C).mono'
      (((conditionalEntropyBranchFiberMass_measurable κ hFm).mul hk.ennreal_toReal).aestronglyMeasurable)
    apply Eventually.of_forall
    intro a
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hmass0 a) ENNReal.toReal_nonneg)]
    exact hmg a
  have hgi : Integrable (fun a => (klDiv (η a) (κ a)).toReal) R :=
    (conditionalEntropyBranch_outer_integrable_iff μ κ hFm hF0 _).mpr hmgi
  have hcost : klDiv (R ⊗ₘ η) (R ⊗ₘ κ) ≠ ∞ := by
    rw [conditionalEntropyBranch_compProd_kl_integral η κ R]
    exact (integrable_toReal_iff hk.aemeasurable (Eventually.of_forall hfinite)).mp hgi
  rw [conditionalEntropyBranch_density_disintegration μ κ hFm hF0 hFi hF hmass]
  refine ⟨hcost, ?_⟩
  change (klDiv (R ⊗ₘ η) (R ⊗ₘ κ)).toReal ≤ _
  rw [conditionalEntropyBranch_compProd_kl_integral_real η κ R hcost]
  calc
    (∫ a, (klDiv (η a) (κ a)).toReal ∂R) =
        ∫ a, conditionalEntropyBranchFiberMass κ F a * (klDiv (η a) (κ a)).toReal ∂μ :=
      conditionalEntropyBranch_outer_integral μ κ hFm hF0 _
    _ ≤ ∫ a, C * E a ∂μ := integral_mono hmgi (hE.const_mul C) hmg
    _ = C * (∫ a, E a ∂μ) := integral_const_mul C E

end RepulsiveCoulomb
