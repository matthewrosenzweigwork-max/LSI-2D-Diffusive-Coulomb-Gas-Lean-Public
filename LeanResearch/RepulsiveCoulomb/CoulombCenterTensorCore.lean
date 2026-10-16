import LeanResearch.RepulsiveCoulomb.CoulombCenterCoreEnergy
import LeanResearch.RepulsiveCoulomb.CoulombCenterTensorEntropy
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoreClosure
import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalLSIRate

/-! Exact tensorization from the two literal factor-core inequalities to every
member of the original closed many-particle form. The hypotheses are the two
factor inequalities to be tensorized, not substitute analytic assumptions in
the final center-of-mass theorem. No loss occurs in the energy coefficient. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open PeriodicAttractiveLogGas
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

def CoulombCenterGaussianCoreLSI (β C : ℝ) : Prop :=
  ∀ ψ : TestFunction (⊤ : Opens ℂ) ℝ ⊤,
    entropy (coulombCenterGaussian β) (fun c => ψ c ^ 2) ≤
      ((C * (∫ c, ‖gradient (ψ : ℂ → ℝ) c‖ ^ 2 ∂coulombCenterGaussian β) : ℝ) : EReal)

def CoulombCenterRelativeCoreLSI (e : CoulombCenterRotation n) (β C : ℝ) : Prop :=
  ∀ ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤,
    entropy (coulombCenterRelativeMeasure e β) (fun r => ψ r ^ 2) ≤
      ((C * (∫ r, ‖gradient (ψ : CoulombConfig n → ℝ) r‖ ^ 2
        ∂coulombCenterRelativeMeasure e β) : ℝ) : EReal)

theorem coulombCenter_normalized_core_tensorization (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β C : ℝ} (hβ : 0 < β)
    (hG : CoulombCenterGaussianCoreLSI β C) (hR : CoulombCenterRelativeCoreLSI e β C)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure (n + 1) β) = 1) :
    entropy (coulombMeasure (n + 1) β) (fun z => φ z ^ 2) ≤
      ((C * (∫ z, ‖gradient (φ : CoulombConfig (n + 1) → ℝ) z‖ ^ 2
        ∂coulombMeasure (n + 1) β) : ℝ) : EReal) := by
  let μ := coulombCenterGaussian β
  let ν := coulombCenterRelativeMeasure e β
  letI := coulombMeasure_isProbability (N := n + 1) hβ
  letI : IsProbabilityMeasure μ := coulombCenterGaussian_isProbability hβ
  letI : IsProbabilityMeasure ν := coulombCenterRelativeMeasure_isProbability e he hβ
  let f : ℂ × CoulombConfig n → ℝ := fun p => φ (coulombCenterInsert e p.1 p.2)
  have hfm : Measurable f := by
    have h := φ.continuous.measurable.comp (coulombCenterChart e).symm.measurable
    simpa only [Function.comp_def, coulombCenterChart_symm_function] using h
  obtain ⟨B, hBpos, hB⟩ := coulomb_testFunction_c1_bound φ
  have hfb : ∀ p, |f p| ≤ B := fun p => (hB (coulombCenterInsert e p.1 p.2)).1
  have hfi : Integrable (fun p => f p ^ 2) (μ.prod ν) :=
    Rothaus.integrable_continuous_comp_bounded hfm hfb (continuous_id.pow 2)
  have hm : (∫ p, f p ^ 2 ∂μ.prod ν) = 1 := by
    have h := (coulombCenter_gibbsMeasurePreserving e he hβ).symm.integral_comp'
      (fun z => φ z ^ 2)
    have hh : (∫ p, f p ^ 2 ∂μ.prod ν) = ∫ z, φ z ^ 2 ∂coulombMeasure (n + 1) β := by
      simpa only [f, μ, ν, Function.comp_def, coulombCenterChart_symm_function] using h
    exact hh.trans hmass
  have hAi (r : CoulombConfig n) : Integrable (fun c => f (c, r) ^ 2) μ :=
    Rothaus.integrable_continuous_comp_bounded (hfm.comp measurable_prodMk_right)
      (fun c => hfb (c, r)) (continuous_id.pow 2)
  have hAl (r : CoulombConfig n) :
      Integrable (fun c => f (c, r) ^ 2 * Real.log (f (c, r) ^ 2)) μ :=
    Rothaus.integrable_continuous_comp_bounded (hfm.comp measurable_prodMk_right)
      (fun c => hfb (c, r)) (Real.continuous_mul_log.comp (continuous_id.pow 2))
  have hBi (c : ℂ) : Integrable (fun r => f (c, r) ^ 2) ν :=
    Rothaus.integrable_continuous_comp_bounded (hfm.comp measurable_prodMk_left)
      (fun r => hfb (c, r)) (continuous_id.pow 2)
  have hBl (c : ℂ) :
      Integrable (fun r => f (c, r) ^ 2 * Real.log (f (c, r) ^ 2)) ν :=
    Rothaus.integrable_continuous_comp_bounded (hfm.comp measurable_prodMk_left)
      (fun r => hfb (c, r)) (Real.continuous_mul_log.comp (continuous_id.pow 2))
  let EA : CoulombConfig n → ℝ := fun r => ∫ c, coulombCenterCoreCenterEnergy e φ (c, r) ∂μ
  let EB : ℂ → ℝ := fun c => ∫ r, coulombCenterCoreRelativeEnergy e φ (c, r) ∂ν
  have hEA : Integrable EA ν :=
    (coulombCenterCoreCenterEnergy_integrable e he hβ φ).integral_prod_right
  have hEB : Integrable EB μ :=
    (coulombCenterCoreRelativeEnergy_integrable e he hβ φ).integral_prod_left
  have hAb (r : CoulombConfig n) : entropy μ (fun c => f (c, r) ^ 2) ≤
      ((C * EA r : ℝ) : EReal) := by
    have h := hG (coulombCenterGaussianCore e φ r)
    simpa only [μ, f, EA, coulombCenterGaussianCore_apply,
      coulombCenterGaussianCore_gradient, coulombCenterCoreCenterEnergy] using h
  have hBb (c : ℂ) : entropy ν (fun r => f (c, r) ^ 2) ≤
      ((C * EB c : ℝ) : EReal) := by
    have h := hR (coulombCenterRelativeCore e he φ c)
    simpa only [ν, f, EB, coulombCenterRelativeCore_apply,
      coulombCenterRelativeCore_gradient, coulombCenterCoreRelativeEnergy] using h
  have ht := coulombCenter_normalized_tensor_entropy μ ν (hfm.pow_const 2)
    (fun p => sq_nonneg (f p)) hAi hAl hBi hBl hfi hm hEA hEB C hAb hBb
  have hEnt : entropy (coulombMeasure (n + 1) β) (fun z => φ z ^ 2) =
      entropy (μ.prod ν) (fun p => f p ^ 2) := by
    have h := coulombCenter_entropy_transport e he hβ (fun p => f p ^ 2)
    have hf : (fun z => f (coulombCenterChart e z) ^ 2) = (fun z => φ z ^ 2) := by
      funext z
      unfold f
      rw [← coulombCenterChart_symm_apply, MeasurableEquiv.symm_apply_apply]
    rw [hf] at h
    exact h
  rw [← hEnt] at ht
  have henergy : (∫ r, EA r ∂ν) + (∫ c, EB c ∂μ) =
      ∫ z, ‖gradient (φ : CoulombConfig (n + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (n + 1) β :=
    coulombCenterCoreEnergy_fubini e he hβ φ
  rw [henergy] at ht
  exact ht

/-- Exact lower-rate tensorization on the FULL original closed form domain. -/
theorem coulombCenter_full_tensorization (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    (hG : CoulombCenterGaussianCoreLSI β C) (hR : CoulombCenterRelativeCoreLSI e β C)
    (u : CoulombFormDomain (n + 1) hβ) :
    entropy (coulombMeasure (n + 1) β)
      (fun z => (coulombFormValueL (n + 1) hβ u z) ^ 2) ≤
      ((C * coulombFormEnergy (n + 1) hβ u : ℝ) : EReal) := by
  have hc (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) :=
    conditionalEntropyBranch_core_denormalize (D := 0) hβ hC le_rfl
      (fun ψ hψ => by simpa only [add_zero] using
        coulombCenter_normalized_core_tensorization e he hβ hG hR ψ hψ) φ
  have hf := conditionalEntropyBranch_form_of_core (D := 0) hβ hc u
  simpa only [zero_mul, add_zero] using hf

/-- The admissible rate is precisely the common factor rate, without loss. -/
theorem coulombCenter_admissible_of_factor_cores (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hG : CoulombCenterGaussianCoreLSI β (2 / ρ))
    (hR : CoulombCenterRelativeCoreLSI e β (2 / ρ)) :
    poleBranchAdmissibleLSIRate (n + 1) hβ ρ :=
  ⟨hρ, coulombCenter_full_tensorization e he hβ (by positivity) hG hR⟩

end RepulsiveCoulomb
