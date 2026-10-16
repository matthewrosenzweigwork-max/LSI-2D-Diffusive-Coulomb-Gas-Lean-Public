module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GibbsProductPower
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGibbsDefectMoment

@[expose] public section

/-! Additive repair source; validation is recorded separately. Actual Gibbs moment proof with a genuine
one-body integrability input. No old whole-plane-normalizer or old moment
producer is selected; the physical reference and canonical law are unchanged.
The later disk producer must discharge this analytic input. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

/-- The exact Gibbs exponential-moment estimate in particle coordinates. The
reference moment and both partition integrals are genuine finite integrals. -/
theorem paper_gibbs_defect_moment_of_oneBody {β ℓ : ℝ} (hβ : 0 < β) (_hℓ : 0 < ℓ)
    (R : EquilibriumConstructedReference β)
    (hU : Integrable (fun x : ℂ => Real.exp (-(2 * ℓ) * β *
      equilibriumDensityPotential R.density x)) (R.measure : Measure ℂ))
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z))
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) ∧
    (∫ z : Fin N → ℂ, Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z)
      ∂Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (2 * (1 + ℓ) * β) R) ^ (1 / 2 : ℝ) *
          (∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
            ∂R.measure) ^ (1 / 2 : ℝ) :=
  paper_gibbs_defect_moment_via_concavity hβ _hℓ R hU hN

/-- Physical l2 configuration formulation, suitable for the canonical
conditional-entropy theorem without changing coordinate or gradient norms. -/
theorem paper_physical_gibbs_defect_moment_of_oneBody {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : 0 < ℓ) (R : EquilibriumConstructedReference β)
    (hU : Integrable (fun x : ℂ => Real.exp (-(2 * ℓ) * β *
      equilibriumDensityPotential R.density x)) (R.measure : Measure ℂ))
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : CoulombConfig N => Real.exp (-ℓ * β *
      (equilibriumModulatedEnergy R.density (@WithLp.ofLp 2 (Fin N → ℂ) z) +
        (∑ i : Fin N, equilibriumDensityPotential R.density (z i)) / (N : ℝ)))) (coulombMeasure N β) ∧
    (∫ z : CoulombConfig N, Real.exp (-ℓ * β *
      (equilibriumModulatedEnergy R.density (@WithLp.ofLp 2 (Fin N → ℂ) z) +
        (∑ i : Fin N, equilibriumDensityPotential R.density (z i)) / (N : ℝ))) ∂coulombMeasure N β) ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (2 * (1 + ℓ) * β) R) ^ (1 / 2 : ℝ) *
          (∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
            ∂R.measure) ^ (1 / 2 : ℝ) := by
  obtain ⟨hi, hb⟩ := paper_gibbs_defect_moment_of_oneBody hβ hℓ R hU hN
  have hp : MeasurePreserving (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) :=
    ⟨WithLp.measurable_ofLp 2 _, rfl⟩
  have hiPhysical := hp.integrable_comp_of_integrable hi
  have hIntegral := hp.integral_comp (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm.measurableEmbedding
    (fun z : Fin N → ℂ => Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z))
  have hbPhysical := hIntegral.trans_le hb
  simpa only [Function.comp_def, equilibriumDefectEnergy] using And.intro hiPhysical hbPhysical

end RepulsiveCoulomb.PaperRoute
