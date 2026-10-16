import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFreeEnergyCorrespondence
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCoercivity

/-! Exact finite-domain bridge from literal densities and their actual product
integrals to the canonical extended free energy. This supports genuine
mass-preserving variations without silently equating a supplied density with
the pointwise RN representative. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumExtendedIntegral_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (h : f =ᵐ[μ] g) :
    equilibriumExtendedIntegral μ f = equilibriumExtendedIntegral μ g := by
  unfold equilibriumExtendedIntegral
  rw [lintegral_congr_ae (h.mono (fun x hx => congrArg ENNReal.ofReal hx)),
    lintegral_congr_ae (h.mono (fun x hx => congrArg (fun t : ℝ => ENNReal.ofReal (-t)) hx))]

theorem equilibriumReferenceDensity_densityMeasure_ae {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    equilibriumReferenceDensity (equilibriumDensityMeasure ρ) =ᵐ[volume] ρ := by
  have h := Measure.rnDeriv_withDensity volume hρm.ennreal_ofReal
  exact h.mono (fun x hx => by
    change ((volume.withDensity (fun z => ENNReal.ofReal (ρ z))).rnDeriv volume x).toReal = ρ x
    rw [hx, ENNReal.toReal_ofReal (hρ0 x)])

/-- Actual product-measure energy integrability for the supplied density. -/
theorem equilibriumDensityMeasure_logEnergy_integrable {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) := by
  unfold equilibriumDensityMeasure
  rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal]
  apply (integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))).mpr
  apply hG.congr
  exact Eventually.of_forall (fun p => by
    dsimp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ0 p.1), ENNReal.toReal_ofReal (hρ0 p.2)]
    ring)

/-- The literal iterated potential energy equals the justified product energy. -/
theorem equilibriumDensityInteraction_eq_product {ρ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    equilibriumDensityInteraction ρ =
      ∫ p : ℂ × ℂ, ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2) ∂volume.prod volume := by
  rw [integral_prod _ hG]
  unfold equilibriumDensityInteraction equilibriumDensityPotential
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (∫ y : ℂ, equilibriumLogKernel (x - y) * ρ y) * ρ x =
      ∫ y : ℂ, ρ x * (equilibriumLogKernel (x - y) * ρ y)
    rw [integral_const_mul]
    ring)

theorem integral_equilibriumDensityMeasure_logEnergy {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(equilibriumDensityMeasure ρ).prod (equilibriumDensityMeasure ρ)) =
        equilibriumDensityInteraction ρ := by
  rw [equilibriumDensityInteraction_eq_product hG]
  unfold equilibriumDensityMeasure
  rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    dsimp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ0 p.1), ENNReal.toReal_ofReal (hρ0 p.2), smul_eq_mul]
    ring)

/-- Exact canonical density bridge, for every beta>0 and every actual finite
energy probability density; no boundedness or regularity is assumed. -/
theorem equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy {β : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) =
      (equilibriumDensityFreeEnergy β ρ : EReal) := by
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  have hP2 := (equilibriumDensityMeasure_integrable_iff hρm hρ0 (fun x : ℂ => ‖x‖ ^ 2)).mpr hρ2
  have hAC := equilibriumDensityMeasure_absolutelyContinuous ρ
  have hkernel := equilibriumDensityMeasure_logEnergy_integrable hρm hρ0 hG
  have hHae : (fun x : ℂ => equilibriumReferenceDensity (equilibriumDensityMeasure ρ) x *
      Real.log (equilibriumReferenceDensity (equilibriumDensityMeasure ρ) x)) =ᵐ[volume]
        (fun x : ℂ => ρ x * Real.log (ρ x)) :=
    (equilibriumReferenceDensity_densityMeasure_ae hρm hρ0).mono
      (fun x hx => by
        change equilibriumReferenceDensity (equilibriumDensityMeasure ρ) x *
          Real.log (equilibriumReferenceDensity (equilibriumDensityMeasure ρ) x) =
            ρ x * Real.log (ρ x)
        rw [hx])
  rw [equilibriumCanonicalFreeEnergy, if_pos ⟨hAC, hP2⟩,
    equilibriumExtendedIntegral_congr_ae hHae, equilibriumExtendedIntegral_eq_integral hρH,
    equilibriumExtendedIntegral_eq_integral hkernel,
    integral_equilibriumDensityMeasure_logEnergy hρm hρ0 hG,
    integral_equilibriumDensityMeasure hρm hρ0]
  simp only [← EReal.coe_mul, ← EReal.coe_add]
  congr 1
  unfold equilibriumDensityFreeEnergy
  rw [show (fun x : ℂ => ρ x * ‖x‖ ^ 2) = (fun x : ℂ => ‖x‖ ^ 2 * ρ x) by funext x; ring]
  ring

end RepulsiveCoulomb
