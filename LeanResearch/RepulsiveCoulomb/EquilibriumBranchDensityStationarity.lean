module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityTiltAdmissible
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchStationaryConstant
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! Derivation of stationarity from genuine canonical minimization, using
admissible finite-energy density tilts and the physical free-energy derivative.
The chemical potential is integrable and is identified with an actual finite
constant under the base law. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def equilibriumChemicalPotential (β : ℝ) (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x + Real.log (ρ x) / β

theorem equilibriumDensityPotential_weight_integrable {ρ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    Integrable (fun x : ℂ => equilibriumDensityPotential ρ x * ρ x) := by
  apply hG.integral_prod_left.congr
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [integral_const_mul]
    unfold equilibriumDensityPotential
    ring)

theorem equilibriumChemicalPotential_integrable (β : ℝ) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    Integrable (equilibriumChemicalPotential β ρ) (equilibriumDensityMeasure ρ) := by
  apply (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr
  have hi := ((hρ2.div_const 2).add (equilibriumDensityPotential_weight_integrable hG)).add
    (hρH.div_const β)
  apply hi.congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply, equilibriumChemicalPotential]; ring)

/-- Exact identification of the derivative coefficient with its integral
against the chemical potential of the actual density measure. -/
theorem integral_equilibriumChemicalPotential_test (β : ℝ) {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hφm : Measurable φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M) :
    (∫ x : ℂ, equilibriumChemicalPotential β ρ x * φ x ∂equilibriumDensityMeasure ρ) =
      (∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x) / 2 +
        (∫ x : ℂ, φ x * (equilibriumDensityPotential ρ x * ρ x)) +
        (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x) / β := by
  have hb : ∀ᵐ x : ℂ, ‖φ x‖ ≤ M := Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using hφM x)
  have h₁ := hρ2.mul_bdd hφm.aestronglyMeasurable hb
  have h₂ := (equilibriumDensityPotential_weight_integrable hG).bdd_mul hφm.aestronglyMeasurable hb
  have h₃ := hρH.mul_bdd hφm.aestronglyMeasurable hb
  rw [integral_equilibriumDensityMeasure hρm hρ0]
  have he : (fun x : ℂ => ρ x * (equilibriumChemicalPotential β ρ x * φ x)) =
      (fun x : ℂ => ((‖x‖ ^ 2 * ρ x) * φ x) / 2 +
        φ x * (equilibriumDensityPotential ρ x * ρ x) + ((ρ x * Real.log (ρ x)) * φ x) / β) := by
    funext x
    unfold equilibriumChemicalPotential
    ring
  have hA := integral_add (h₁.div_const 2) h₂
  have hB := integral_add ((h₁.div_const 2).add h₂) (h₃.div_const β)
  dsimp only [Pi.add_apply] at hA hB
  rw [he, hB, hA, integral_div, integral_div]

/-- Canonical minimization forces the genuine physical first variation to
vanish. Every nearby competitor is explicitly a probability measure with all
ordinary energy integrals finite before the canonical bridge is applied. -/
theorem equilibriumDensityMinimizer_firstVariation_zero {β : ℝ} (hβ : 0 < β)
    {ρ φ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤ equilibriumCanonicalFreeEnergy β ν)
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M)
    (hφzero : (∫ x : ℂ, φ x ∂equilibriumDensityMeasure ρ) = 0) :
    (∫ x : ℂ, equilibriumChemicalPotential β ρ x * φ x ∂equilibriumDensityMeasure ρ) = 0 := by
  let F : ℝ → ℝ := fun t => equilibriumDensityFreeEnergy β (equilibriumDensityTilt t ρ φ)
  have hF0 : F 0 = equilibriumDensityFreeEnergy β ρ := by
    dsimp only [F]
    have h0 : equilibriumDensityTilt 0 ρ φ = ρ := by funext x; simp only [equilibriumDensityTilt, zero_mul, add_zero, one_mul]
    rw [h0]
  have hδ : 0 < 1 / (2 * (M + 1)) := by positivity
  have hlocal : IsLocalMin F 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), F 0 ≤ F t
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with t ht
    let ψ : ℂ → ℝ := equilibriumDensityTilt t ρ φ
    have hψm : Measurable ψ := equilibriumDensityTilt_measurable t hρm hφm
    have hψ0 : ∀ x, 0 ≤ ψ x := equilibriumDensityTilt_nonneg hρ0 hM hφM ht
    have hψi : Integrable ψ := equilibriumDensityTilt_integrable t hρi hφm hφM
    have hψmass : (∫ x : ℂ, ψ x) = 1 := integral_equilibriumDensityTilt t hρm hρ0 hρi hρmass hφm hφM hφzero
    have hψ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ψ x) :=
      equilibriumDensityTilt_secondMoment_integrable t hρ2 hφm hφM
    have hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)) :=
      (equilibrium_density_tilt_entropy_identity hρm hρ0 hρi hρmass hρH hφm hM hφM ht).1
    have hψG := equilibriumDensityTilt_logEnergy_integrable t hG hφm hM hφM
    letI := equilibriumDensityMeasure_probability hψ0 hψi hψmass
    let ν : ProbabilityMeasure ℂ := ⟨equilibriumDensityMeasure ψ, inferInstance⟩
    have hc := hmin ν
    change equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ψ) at hc
    rw [equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hρm hρ0 hρi hρmass hρ2 hρH hG,
      equilibriumCanonicalFreeEnergy_eq_densityFreeEnergy hβ hψm hψ0 hψi hψmass hψ2 hψH hψG] at hc
    rw [hF0]
    exact EReal.coe_le_coe_iff.mp hc
  have hd := equilibrium_hasDerivAt_density_tilt_freeEnergy β hρm hρ0 hρi hρmass hρ2 hρH hG
    hφm hM hφM hφzero
  rw [integral_equilibriumChemicalPotential_test β hρm hρ0 hρ2 hρH hG hφm hφM]
  exact hlocal.hasDerivAt_eq_zero hd

/-- The chemical potential of an actual finite-energy canonical minimizing
density is constant under its actual probability law. -/
theorem equilibriumDensityMinimizer_chemicalPotential_constant {β : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β (equilibriumDensityMeasure ρ) ≤ equilibriumCanonicalFreeEnergy β ν) :
    equilibriumChemicalPotential β ρ =ᵐ[equilibriumDensityMeasure ρ]
      (fun _ => ∫ x : ℂ, equilibriumChemicalPotential β ρ x ∂equilibriumDensityMeasure ρ) := by
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  apply equilibrium_stationary_integrable_ae_constant
    (equilibriumChemicalPotential_integrable β hρm hρ0 hρ2 hρH hG)
  intro φ hφm hφb hφzero
  exact equilibriumDensityMinimizer_firstVariation_zero hβ hρm hρ0 hρi hρmass hρ2 hρH hG hmin
    hφm zero_le_one hφb hφzero

end RepulsiveCoulomb
