import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalBoundedRepresentative
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityRepulsivity

/-! Uniqueness through strict entropy monotonicity and actual logarithmic
repulsivity. The cross and self energies are proved absolutely integrable
using the checked bounded-density estimates. Bounded positive pointwise-EL
representatives are constructed in the preceding module, not assumed for the
thermal minimizer in the final application. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Strict monotonicity of log is the strict-entropy input. -/
theorem equilibrium_log_monotonicity_product {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 ≤ (r - s) * (Real.log r - Real.log s) := by
  rcases le_total r s with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.log_le_log hr h))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.log_le_log hs h))

theorem equilibrium_log_monotonicity_product_eq_zero {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : (r - s) * (Real.log r - Real.log s) = 0) : r = s := by
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact (Real.log_injOn_pos hr hs (sub_eq_zero.mp h))

/-- Actual row integrability of a cross potential, after product-space energy
integrability has been established. -/
theorem equilibriumDensityCrossPotential_integrable {ρ σ : ℂ → ℝ}
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * σ p.2)) (volume.prod volume)) :
    Integrable (fun x : ℂ => ρ x * equilibriumDensityPotential σ x) := by
  apply hRS.integral_prod_left.congr
  exact Eventually.of_forall (fun x => by
    change (∫ y : ℂ, ρ x * (equilibriumLogKernel (x - y) * σ y)) =
      ρ x * equilibriumDensityPotential σ x
    rw [integral_const_mul]
    rfl)

theorem equilibriumDensityCrossIntegral_eq_potential {ρ σ : ℂ → ℝ}
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * σ p.2)) (volume.prod volume)) :
    equilibriumDensityCrossIntegral ρ σ = ∫ x : ℂ, ρ x * equilibriumDensityPotential σ x := by
  unfold equilibriumDensityCrossIntegral
  rw [integral_prod _ hRS]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (∫ y : ℂ, ρ x * (equilibriumLogKernel (x - y) * σ y)) =
      ρ x * equilibriumDensityPotential σ x
    rw [integral_const_mul]
    rfl)

/-- The density/potential pairing has the same finite quadratic expansion as
the actual signed product-space energy. -/
theorem equilibriumDensityDifference_potential_energy {ρ σ : ℂ → ℝ}
    (hRR : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * σ p.2)) (volume.prod volume))
    (hSS : Integrable (fun p : ℂ × ℂ => σ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * σ p.2)) (volume.prod volume)) :
    Integrable (fun x : ℂ => (ρ x - σ x) *
      (equilibriumDensityPotential ρ x - equilibriumDensityPotential σ x)) ∧
    (∫ x : ℂ, (ρ x - σ x) * (equilibriumDensityPotential ρ x - equilibriumDensityPotential σ x)) =
      ∫ p : ℂ × ℂ, (ρ p.1 - σ p.1) * (ρ p.2 - σ p.2) *
        equilibriumLogKernel (p.1 - p.2) ∂volume.prod volume := by
  have hSR := equilibriumDensityCross_integrable_swap hRS
  have hiRR := equilibriumDensityCrossPotential_integrable hRR
  have hiRS := equilibriumDensityCrossPotential_integrable hRS
  have hiSR := equilibriumDensityCrossPotential_integrable hSR
  have hiSS := equilibriumDensityCrossPotential_integrable hSS
  have hp : (fun x : ℂ => (ρ x - σ x) *
      (equilibriumDensityPotential ρ x - equilibriumDensityPotential σ x)) =
      (fun x : ℂ => ((ρ x * equilibriumDensityPotential ρ x - ρ x * equilibriumDensityPotential σ x) -
        σ x * equilibriumDensityPotential ρ x) + σ x * equilibriumDensityPotential σ x) := by
    funext x
    ring
  have he : (fun p : ℂ × ℂ => (ρ p.1 - σ p.1) * (ρ p.2 - σ p.2) * equilibriumLogKernel (p.1 - p.2)) =
      (fun p : ℂ × ℂ => ((ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2) -
        ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * σ p.2)) -
        σ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) +
        σ p.1 * (equilibriumLogKernel (p.1 - p.2) * σ p.2)) := by
    funext p
    ring
  refine ⟨?_, ?_⟩
  · rw [hp]
    exact ((hiRR.sub hiRS).sub hiSR).add hiSS
  · have hp₁ := integral_sub hiRR hiRS
    have hp₂ := integral_sub (hiRR.sub hiRS) hiSR
    have hp₃ := integral_add ((hiRR.sub hiRS).sub hiSR) hiSS
    have he₁ := integral_sub hRR hRS
    have he₂ := integral_sub (hRR.sub hRS) hSR
    have he₃ := integral_add ((hRR.sub hRS).sub hSR) hSS
    dsimp only [Pi.sub_apply] at hp₁ hp₂ hp₃ he₁ he₂ he₃
    rw [hp, he, hp₃, hp₂, hp₁, he₃, he₂, he₁]
    rw [← equilibriumDensityCrossIntegral_eq_potential hRR,
      ← equilibriumDensityCrossIntegral_eq_potential hRS,
      ← equilibriumDensityCrossIntegral_eq_potential hSR,
      ← equilibriumDensityCrossIntegral_eq_potential hSS]
    rfl

/-- Positive bounded probability densities satisfying the same-beta EL
equation and having finite logarithmic moments agree almost everywhere. -/
theorem equilibrium_pointwise_EL_densities_unique {β Cρ Cσ Mρ Mσ : ℝ} (hβ : 0 < β)
    {ρ σ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ Mρ)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρL : Integrable (fun x : ℂ => equilibriumLogMoment x * ρ x))
    (hσm : Measurable σ) (hσpos : ∀ x, 0 < σ x) (hσM : ∀ x, σ x ≤ Mσ)
    (hσi : Integrable σ) (hσmass : (∫ x : ℂ, σ x) = 1)
    (hσL : Integrable (fun x : ℂ => equilibriumLogMoment x * σ x))
    (hELρ : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + Cρ)
    (hELσ : ∀ x, Real.log (σ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential σ x) + Cσ) :
    ρ =ᵐ[volume] σ := by
  have hρ0 := fun x => (hρpos x).le
  have hσ0 := fun x => (hσpos x).le
  have hRR := equilibriumCrossInteraction_integrable hρm hρ0 hρi hρL hρm hρ0 hρM hρi hρmass hρL
  have hRS := equilibriumCrossInteraction_integrable hρm hρ0 hρi hρL hσm hσ0 hσM hσi hσmass hσL
  have hSS := equilibriumCrossInteraction_integrable hσm hσ0 hσi hσL hσm hσ0 hσM hσi hσmass hσL
  obtain ⟨hpi, hpe⟩ := equilibriumDensityDifference_potential_energy hRR hRS hSS
  have hp0 : 0 ≤ ∫ x : ℂ, (ρ x - σ x) *
      (equilibriumDensityPotential ρ x - equilibriumDensityPotential σ x) := by
    rw [hpe]
    exact equilibriumDensityDifference_repulsive hρm hρ0 hρM hρi hρmass hρL
      hσm hσ0 hσM hσi hσmass hσL
  have he : (fun x : ℂ => (ρ x - σ x) * (Real.log (ρ x) - Real.log (σ x))) =
      (fun x : ℂ => -β * ((ρ x - σ x) *
        (equilibriumDensityPotential ρ x - equilibriumDensityPotential σ x)) +
          (Cρ - Cσ) * (ρ x - σ x)) := by
    funext x
    rw [hELρ x, hELσ x]
    ring
  have hd : Integrable (fun x : ℂ => ρ x - σ x) := hρi.sub hσi
  have hi : Integrable (fun x : ℂ => (ρ x - σ x) * (Real.log (ρ x) - Real.log (σ x))) := by
    rw [he]
    exact (hpi.const_mul (-β)).add (hd.const_mul (Cρ - Cσ))
  have hmass : (∫ x : ℂ, ρ x - σ x) = 0 := by
    rw [integral_sub hρi hσi, hρmass, hσmass, sub_self]
  have hle : (∫ x : ℂ, (ρ x - σ x) * (Real.log (ρ x) - Real.log (σ x))) ≤ 0 := by
    rw [he, integral_add (hpi.const_mul (-β)) (hd.const_mul (Cρ - Cσ)),
      integral_const_mul, integral_const_mul, hmass, mul_zero, add_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) hp0
  have hz : (∫ x : ℂ, (ρ x - σ x) * (Real.log (ρ x) - Real.log (σ x))) = 0 :=
    le_antisymm hle (integral_nonneg (fun x => equilibrium_log_monotonicity_product (hρpos x) (hσpos x)))
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => equilibrium_log_monotonicity_product (hρpos x) (hσpos x)) hi).mp hz
  exact hae.mono (fun x hx => equilibrium_log_monotonicity_product_eq_zero (hρpos x) (hσpos x) hx)

/-- Uniqueness is a conclusion for actual finite-objective minimizers: the
bounded pointwise-EL densities are constructed before repulsivity is invoked. -/
theorem equilibriumCanonicalMinimizers_unique {β : ℝ} (hβ : 0 < β)
    (μ ν : ProbabilityMeasure ℂ)
    (hμfinite : equilibriumNonnegativeObjective β μ ≠ ∞)
    (hνfinite : equilibriumNonnegativeObjective β ν ≠ ∞)
    (hμmin : ∀ ξ : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ξ)
    (hνmin : ∀ ξ : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β ν ≤ equilibriumCanonicalFreeEnergy β ξ) : μ = ν := by
  obtain ⟨ρ, Cρ, Mρ, Kρ, hρm, hρpos, hMρ, hρM, hρi, hρmass, hρ2, hρH, hρμ, hELρ, hKρ, htailρ⟩ :=
    equilibriumCanonicalMinimizer_exists_bounded_EL_density hβ μ hμfinite hμmin
  obtain ⟨σ, Cσ, Mσ, Kσ, hσm, hσpos, hMσ, hσM, hσi, hσmass, hσ2, hσH, hσν, hELσ, hKσ, htailσ⟩ :=
    equilibriumCanonicalMinimizer_exists_bounded_EL_density hβ ν hνfinite hνmin
  have hρL := equilibriumLogMoment_mul_integrable hρm (fun x => (hρpos x).le) hρi hρ2
  have hσL := equilibriumLogMoment_mul_integrable hσm (fun x => (hσpos x).le) hσi hσ2
  have he := equilibrium_pointwise_EL_densities_unique hβ hρm hρpos hρM hρi hρmass hρL
    hσm hσpos hσM hσi hσmass hσL hELρ hELσ
  apply Subtype.ext
  change (μ : Measure ℂ) = (ν : Measure ℂ)
  rw [← hρμ, ← hσν]
  unfold equilibriumDensityMeasure
  apply withDensity_congr_ae
  exact he.mono (fun x hx => by simp only [hx])

end RepulsiveCoulomb
