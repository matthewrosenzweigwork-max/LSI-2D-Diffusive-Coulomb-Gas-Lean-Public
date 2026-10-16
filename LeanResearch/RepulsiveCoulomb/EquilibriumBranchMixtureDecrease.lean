module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityMixture
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyMixture

@[expose] public section

/-! Exact canonical-normalized finite free-energy variation for disjoint
probability densities. The entropy gain gives a strict decrease for an actual
small mixture, with all moments and pair integrals kept explicit. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumDensityMixture_secondMoment_integrable (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x)) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumDensityMixture ε ρ ψ x) := by
  apply ((hρ2.const_mul (1 - ε)).add (hψ2.const_mul ε)).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply, equilibriumDensityMixture]; ring)

theorem integral_equilibriumDensityMixture_secondMoment (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x)) :
    (∫ x : ℂ, ‖x‖ ^ 2 * equilibriumDensityMixture ε ρ ψ x) =
      (1 - ε) * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) + ε * (∫ x : ℂ, ‖x‖ ^ 2 * ψ x) := by
  have he : (fun x : ℂ => ‖x‖ ^ 2 * equilibriumDensityMixture ε ρ ψ x) =
      (fun x : ℂ => (1 - ε) * (‖x‖ ^ 2 * ρ x) + ε * (‖x‖ ^ 2 * ψ x)) := by
    funext x
    unfold equilibriumDensityMixture
    ring
  rw [he, integral_add (hρ2.const_mul (1 - ε)) (hψ2.const_mul ε),
    integral_const_mul, integral_const_mul]

theorem equilibriumDensityFreeEnergy_mixture_difference {β ε : ℝ} {ρ ψ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hψ0 : ∀ x, 0 ≤ ψ x) (hdisj : ∀ᵐ x : ℂ, ρ x * ψ x = 0)
    (hρi : Integrable ρ) (hψi : Integrable ψ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) (hψmass : (∫ x : ℂ, ψ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)))
    (hRR : Integrable (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume))
    (hSS : Integrable (fun p : ℂ × ℂ => ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume))
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    equilibriumDensityFreeEnergy β (equilibriumDensityMixture ε ρ ψ) - equilibriumDensityFreeEnergy β ρ =
      ε * (((∫ x : ℂ, ‖x‖ ^ 2 * ψ x) - (∫ x : ℂ, ‖x‖ ^ 2 * ρ x)) / 2 +
        equilibriumDensityCrossIntegral ρ ψ - equilibriumDensityInteraction ρ +
        ((∫ x : ℂ, ψ x * Real.log (ψ x)) - (∫ x : ℂ, ρ x * Real.log (ρ x))) / β) +
      ε ^ 2 * ((equilibriumDensityInteraction ρ - 2 * equilibriumDensityCrossIntegral ρ ψ +
        equilibriumDensityInteraction ψ) / 2) +
      β⁻¹ * ((1 - ε) * Real.log (1 - ε) + ε * Real.log ε) := by
  unfold equilibriumDensityFreeEnergy
  rw [integral_equilibriumDensityMixture_secondMoment ε hρ2 hψ2,
    equilibriumDensityMixture_interaction ε hRR hRS hSS]
  have he := integral_equilibrium_disjoint_entropy_mixture hρ0 hψ0 hdisj hρi hψi hρmass hψmass hρH hψH hε0 hε1
  change (∫ x : ℂ, equilibriumDensityMixture ε ρ ψ x * Real.log (equilibriumDensityMixture ε ρ ψ x)) = _ at he
  rw [he]
  ring

/-- An actual mixture has strictly smaller free energy whenever the original
and filling densities have disjoint support and all displayed finite-domain
conditions. No differentiability of either density is required. -/
theorem equilibriumDensityFreeEnergy_exists_disjoint_decrease {β : ℝ} (hβ : 0 < β)
    {ρ ψ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hψ0 : ∀ x, 0 ≤ ψ x) (hdisj : ∀ᵐ x : ℂ, ρ x * ψ x = 0)
    (hρi : Integrable ρ) (hψi : Integrable ψ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) (hψmass : (∫ x : ℂ, ψ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)))
    (hRR : Integrable (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume))
    (hSS : Integrable (fun p : ℂ × ℂ => ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume)) :
    ∃ ε : ℝ, ε ∈ Ioo 0 1 ∧
      equilibriumDensityFreeEnergy β (equilibriumDensityMixture ε ρ ψ) < equilibriumDensityFreeEnergy β ρ := by
  let B := ((∫ x : ℂ, ‖x‖ ^ 2 * ψ x) - (∫ x : ℂ, ‖x‖ ^ 2 * ρ x)) / 2 +
    equilibriumDensityCrossIntegral ρ ψ - equilibriumDensityInteraction ρ +
    ((∫ x : ℂ, ψ x * Real.log (ψ x)) - (∫ x : ℂ, ρ x * Real.log (ρ x))) / β
  let D := (equilibriumDensityInteraction ρ - 2 * equilibriumDensityCrossIntegral ρ ψ +
    equilibriumDensityInteraction ψ) / 2
  obtain ⟨ε, hε, hdec⟩ := equilibrium_binary_entropy_strict_decrease hβ B D
  refine ⟨ε, hε, ?_⟩
  have he := equilibriumDensityFreeEnergy_mixture_difference (β := β) hρ0 hψ0 hdisj hρi hψi hρmass hψmass
    hρ2 hψ2 hρH hψH hRR hRS hSS hε.1 hε.2
  change equilibriumDensityFreeEnergy β (equilibriumDensityMixture ε ρ ψ) -
    equilibriumDensityFreeEnergy β ρ = ε * B + ε ^ 2 * D +
      β⁻¹ * ((1 - ε) * Real.log (1 - ε) + ε * Real.log ε) at he
  linarith

end RepulsiveCoulomb
