module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchNormalizedKernel
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Disintegration.Unique

@[expose] public section

/-!
Actual disintegration of a normalized nonnegative density over a genuine
composition-product law. The outside marginal is the base marginal weighted
by conditional mass, and the conditional law is the measurable zero-safe
normalization proved in the preceding module. Records-only, unchecked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
  {F : α × β → ℝ}

theorem conditionalEntropyBranchFiberMass_integrable (hF0 : ∀ p, 0 ≤ F p)
    (hF : Integrable F (μ ⊗ₘ κ)) :
    Integrable (conditionalEntropyBranchFiberMass κ F) μ := by
  have h := (Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF |>.2
  change Integrable (fun a => ∫ b, F (a, b) ∂κ a) μ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)] using h

theorem conditionalEntropyBranch_outer_density_probability (hF0 : ∀ p, 0 ≤ F p)
    (hF : Integrable F (μ ⊗ₘ κ)) (hmass : (∫ p, F p ∂μ ⊗ₘ κ) = 1) :
    IsProbabilityMeasure
      (conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F)) := by
  apply conditionalEntropyBranchDensityLaw_probability
    (fun a => integral_nonneg (fun b => hF0 (a, b)))
      (conditionalEntropyBranchFiberMass_integrable μ κ hF0 hF)
  simpa only [conditionalEntropyBranchFiberMass, Measure.integral_compProd hF] using hmass

/-- Genuine measure factorization for an arbitrary normalized density F,
including fibers where its conditional mass vanishes. -/
theorem conditionalEntropyBranch_density_disintegration (hFm : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) (hFi : ∀ a, Integrable (fun b => F (a, b)) (κ a))
    (hF : Integrable F (μ ⊗ₘ κ)) (hmass : (∫ p, F p ∂μ ⊗ₘ κ) = 1) :
    conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F =
      conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F) ⊗ₘ
        conditionalEntropyBranchNormalizedKernel κ hFm := by
  letI := conditionalEntropyBranch_outer_density_probability μ κ hF0 hF hmass
  letI := conditionalEntropyBranchNormalizedKernel_isMarkov κ hFm hF0 hFi
  let η : Kernel α β := κ.withDensity (fun a b => ENNReal.ofReal (F (a, b)))
  letI : IsSFiniteKernel η := Kernel.IsSFiniteKernel.withDensity κ
    (fun _ _ => ENNReal.ofReal_ne_top)
  have he : conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F = μ ⊗ₘ η := by
    exact (Measure.compProd_withDensity (μ := μ) (κ := κ)
      (g := fun a b => ENNReal.ofReal (F (a, b))) hFm.ennreal_ofReal).symm
  rw [he]
  ext s hs
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs]
  change (∫⁻ a, η a (Prod.mk a ⁻¹' s) ∂μ) =
    ∫⁻ a, conditionalEntropyBranchNormalizedKernel κ hFm a (Prod.mk a ⁻¹' s)
      ∂μ.withDensity (fun a => ENNReal.ofReal (conditionalEntropyBranchFiberMass κ F a))
  rw [lintegral_withDensity_eq_lintegral_mul μ
    (conditionalEntropyBranchFiberMass_measurable κ hFm).ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left
        (κ := conditionalEntropyBranchNormalizedKernel κ hFm) hs)]
  apply lintegral_congr
  intro a
  change (κ.withDensity (fun a b => ENNReal.ofReal (F (a, b)))) a (Prod.mk a ⁻¹' s) = _
  rw [Kernel.withDensity_apply (f := fun a b => ENNReal.ofReal (F (a, b)))
    κ hFm.ennreal_ofReal]
  have h := congrArg (fun ν : Measure β => ν (Prod.mk a ⁻¹' s))
    (conditionalEntropyBranch_fiber_mass_smul κ hFm hF0 hFi a).symm
  simpa only [Measure.smul_apply, smul_eq_mul, Pi.mul_apply] using h

theorem conditionalEntropyBranch_density_marginal (hFm : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) (hFi : ∀ a, Integrable (fun b => F (a, b)) (κ a))
    (hF : Integrable F (μ ⊗ₘ κ)) (hmass : (∫ p, F p ∂μ ⊗ₘ κ) = 1) :
    (conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F).fst =
      conditionalEntropyBranchDensityLaw μ (conditionalEntropyBranchFiberMass κ F) := by
  letI := conditionalEntropyBranch_outer_density_probability μ κ hF0 hF hmass
  letI := conditionalEntropyBranchNormalizedKernel_isMarkov κ hFm hF0 hFi
  rw [conditionalEntropyBranch_density_disintegration μ κ hFm hF0 hFi hF hmass,
    Measure.fst_compProd]

/-- Identification with the pinned constructed arbitrary-Q conditional, rather
than a substitution of a different notion of conditional entropy. -/
theorem conditionalEntropyBranch_normalizedKernel_eq_condKernel
    [StandardBorelSpace β] [Nonempty β] (Q : Measure (α × β)) [IsProbabilityMeasure Q]
    (hFm : Measurable F) (hF0 : ∀ p, 0 ≤ F p)
    (hFi : ∀ a, Integrable (fun b => F (a, b)) (κ a))
    (hF : Integrable F (μ ⊗ₘ κ)) (hmass : (∫ p, F p ∂μ ⊗ₘ κ) = 1)
    (hQ : Q = conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F) :
    conditionalEntropyBranchNormalizedKernel κ hFm =ᵐ[Q.fst] Q.condKernel := by
  letI := conditionalEntropyBranchNormalizedKernel_isMarkov κ hFm hF0 hFi
  apply eq_condKernel_of_measure_eq_compProd
  rw [hQ, conditionalEntropyBranch_density_marginal μ κ hFm hF0 hFi hF hmass]
  exact conditionalEntropyBranch_density_disintegration μ κ hFm hF0 hFi hF hmass

end RepulsiveCoulomb
