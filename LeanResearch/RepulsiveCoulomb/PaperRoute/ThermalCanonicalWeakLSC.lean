module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalSplitting
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyWeakLSC
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPositiveIntegralLSC
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

/-! Canonical liminf control through Gaussian KL, the genuine positive singular
part, and the newly proved negative-log uniform integrability theorem. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

theorem thermalGaussianPositiveBlock_lowerSemicontinuous {β : ℝ} (hβ : 0 < β) :
    LowerSemicontinuous (thermalGaussianPositiveBlock β) := by
  have ha : 0 < β / 4 := by positivity
  let := equilibriumGaussianMeasure_probability ha
  have he := equilibrium_klDiv_weak_lowerSemicontinuous (equilibriumGaussianMeasure (β / 4))
  have hew : LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      ENNReal.ofReal β⁻¹ * InformationTheory.klDiv (μ : Measure ℂ)
        (equilibriumGaussianMeasure (β / 4))) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous he
      (fun x y hxy => mul_le_mul_right hxy _)
  have hm := equilibrium_positiveIntegral_lowerSemicontinuous (fun x : ℂ => ‖x‖ ^ 2)
    (continuous_norm.pow 2) (fun x => sq_nonneg ‖x‖)
  have hmw : LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      ENNReal.ofReal (1 / 4 : ℝ) * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous hm
      (fun x y hxy => mul_le_mul_right hxy _)
  have hpw : LowerSemicontinuous (fun μ : ProbabilityMeasure ℂ =>
      ENNReal.ofReal (1 / 2 : ℝ) * thermalPositiveLogInteraction μ) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      thermalPositiveLogInteraction_lowerSemicontinuous (fun x y hxy => mul_le_mul_right hxy _)
  exact (hew.add hmw).add hpw

/-- The new uniform-moment canonical liminf theorem. Limit P2 is derived by the
UI endpoint; AC and finite full energy are not assumptions on the limit. -/
theorem thermalCanonicalFreeEnergy_le_liminf_of_uniform_secondMoment
    {β : ℝ} (hβ : 0 < β)
    {μs : ℕ → ProbabilityMeasure ℂ} {μ : ProbabilityMeasure ℂ} {M : ℝ}
    (hweak : Tendsto μs atTop (𝓝 μ))
    (hP2 : ∀ n, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs n))
    (hM : ∀ n, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs n)) ≤ M) :
    equilibriumCanonicalFreeEnergy β μ ≤
      Filter.liminf (fun n => equilibriumCanonicalFreeEnergy β (μs n)) atTop := by
  obtain ⟨hμ, _, _, hneg⟩ :=
    thermal_negative_log_integral_tendsto_of_uniform_secondMoment hweak hP2 hM
  have hl : LowerSemicontinuous (fun ν : ProbabilityMeasure ℂ =>
      (thermalGaussianPositiveBlock β ν : EReal)) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (thermalGaussianPositiveBlock_lowerSemicontinuous hβ)
      (fun x y hxy => EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxy)
  have hbl : (thermalGaussianPositiveBlock β μ : EReal) ≤
      liminf (fun n => (thermalGaussianPositiveBlock β (μs n) : EReal)) atTop := by
    apply (le_liminf_iff).2
    intro b hb
    exact hweak.eventually ((lowerSemicontinuousAt_iff.mp (hl μ)) b hb)
  let C : ProbabilityMeasure ℂ → ℝ := fun ν => Real.log ((β / 4) / Real.pi) / β -
    (∫ p, thermalNegativeLogKernel p ∂((ν : Measure ℂ).prod ν)) / 2
  have hC : Tendsto (fun n => C (μs n)) atTop (𝓝 (C μ)) :=
    tendsto_const_nhds.sub (hneg.div_const 2)
  have hCE : Tendsto (fun n => (C (μs n) : EReal)) atTop (𝓝 (C μ : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp hC
  have hadd := EReal.le_liminf_add
    (u := fun n => (thermalGaussianPositiveBlock β (μs n) : EReal))
    (v := fun n => (C (μs n) : EReal)) (f := atTop)
  rw [hCE.liminf_eq] at hadd
  have hres := (add_le_add hbl (le_refl (C μ : EReal))).trans hadd
  simpa only [Pi.add_def, C,
    ← thermalCanonicalFreeEnergy_eq_positiveBlock_sub_negative hβ μ hμ,
    ← thermalCanonicalFreeEnergy_eq_positiveBlock_sub_negative hβ _ (hP2 _)] using hres

end RepulsiveCoulomb.PaperRoute
