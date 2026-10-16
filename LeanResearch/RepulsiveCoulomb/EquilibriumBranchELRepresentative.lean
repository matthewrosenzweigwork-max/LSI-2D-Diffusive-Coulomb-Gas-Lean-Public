module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchELTailBound

@[expose] public section

/-! A genuine positive bounded representative satisfying EL at every point.
An a.e. finite-energy EL density is first clipped on a null set, which makes
all its potential rows integrable. The exponential representative is then
shown to agree almost everywhere with the original density and to generate
exactly the same potential everywhere. No smoothness or radiality is assumed. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumELRepresentative (β C : ℝ) (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  Real.exp (-β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)

theorem equilibriumELRepresentative_pos (β C : ℝ) (ρ : ℂ → ℝ) (x : ℂ) :
    0 < equilibriumELRepresentative β C ρ x := Real.exp_pos _

theorem equilibriumELRepresentative_measurable (β C : ℝ) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) : Measurable (equilibriumELRepresentative β C ρ) := by
  have hU := equilibriumDensityPotential_measurable hρm
  unfold equilibriumELRepresentative
  fun_prop

theorem equilibriumELRepresentative_ae_eq {β C : ℝ} {ρ : ℂ → ℝ}
    (hρpos : ∀ᵐ x : ℂ, 0 < ρ x)
    (hEL : ∀ᵐ x : ℂ, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) :
    equilibriumELRepresentative β C ρ =ᵐ[volume] ρ := by
  filter_upwards [hρpos, hEL] with x hxpos hxEL
  unfold equilibriumELRepresentative
  rw [← hxEL, Real.exp_log hxpos]

/-- The actual potential is finite at every point after the derived a.e.
density cap, even for the original RN representative. -/
theorem equilibriumDensity_EL_all_rows_integrable {β C : ℝ} (hβ : 0 < β) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρpos : ∀ᵐ x : ℂ, 0 < ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hEL : ∀ᵐ x : ℂ, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (x : ℂ) : Integrable (fun y : ℂ => equilibriumLogKernel (x - y) * ρ y) := by
  let B : ℝ := Real.exp (C + β * ((∫ y : ℂ, equilibriumLogMoment y * ρ y) + 1))
  let σ : ℂ → ℝ := fun y => min (ρ y) B
  have hB : 0 < B := Real.exp_pos _
  have hb : ∀ᵐ y : ℂ, ρ y ≤ B := equilibriumDensity_EL_bounded_ae hβ hρm hρ0 hρi hρmass hρ2 hρpos hG hEL
  have hσρ : σ =ᵐ[volume] ρ := hb.mono (fun y hy => min_eq_left hy)
  have hσm : Measurable σ := hρm.min measurable_const
  have hσ0 : ∀ y, 0 ≤ σ y := fun y => le_min (hρ0 y) hB.le
  have hσB : ∀ y, σ y ≤ B := fun y => min_le_right _ _
  have hσi : Integrable σ := hρi.congr hσρ.symm
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hσL : Integrable (fun y : ℂ => equilibriumLogMoment y * σ y) :=
    hρL.congr (hσρ.symm.mono (fun y hy => by simp only [hy]))
  apply (equilibriumLogKernel_mul_integrable hσm hσ0 hσB hσi hσL x).congr
  exact hσρ.mono (fun y hy => by simp only [hy])

/-- The exponential representative satisfies EL pointwise with its own
potential and preserves the exact Gaussian-polynomial tail exponent beta. -/
theorem equilibriumELRepresentative_pointwise_properties {β C : ℝ} (hβ : 0 < β) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρpos : ∀ᵐ x : ℂ, 0 < ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hEL : ∀ᵐ x : ℂ, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) :
    let ψ := equilibriumELRepresentative β C ρ
    (∀ x, Real.log (ψ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ψ x) + C) ∧
    (∀ x, ψ x ≤ Real.exp (C + β * (∫ y : ℂ, equilibriumLogMoment y * ρ y)) *
      (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) ∧
    (∀ x, ψ x ≤ Real.exp (C + β * ((∫ y : ℂ, equilibriumLogMoment y * ρ y) + 1))) := by
  let ψ := equilibriumELRepresentative β C ρ
  have hψρ : ψ =ᵐ[volume] ρ := equilibriumELRepresentative_ae_eq hρpos hEL
  have hψEL (x : ℂ) : Real.log (ψ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C :=
    Real.log_exp _
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hU (x : ℂ) : -equilibriumLogMoment x - (∫ y : ℂ, equilibriumLogMoment y * ρ y) ≤
      equilibriumDensityPotential ρ x :=
    equilibriumDensityPotential_lower_of_integrable hρ0 hρi hρmass hρL x
      (equilibriumDensity_EL_all_rows_integrable hβ hρm hρ0 hρi hρmass hρ2 hρpos hG hEL x)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [equilibriumDensityPotential_congr_ae hψρ x]
    exact hψEL x
  · intro x
    exact equilibrium_EL_polynomial_gaussian_bound hβ (equilibriumELRepresentative_pos β C ρ x) x
      (hψEL x) (hU x)
  · intro x
    have hb := equilibrium_EL_gaussian_bound hβ (equilibriumELRepresentative_pos β C ρ x) x
      (hψEL x) (hU x)
    have he : Real.exp (-β * ‖x‖ ^ 2 / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
    exact hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

end RepulsiveCoulomb
