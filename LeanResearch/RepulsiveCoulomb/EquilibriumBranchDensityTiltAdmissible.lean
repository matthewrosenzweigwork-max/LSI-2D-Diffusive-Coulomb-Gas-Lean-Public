import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityTiltInteraction

/-! Finite-domain admissibility and the actual first derivative of the
manuscript free energy along bounded zero-mass density tilts. These are
consequences of finite entropy, moment and absolute pair energy, all of which
are derived from the nonnegative objective for the eventual minimizer. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumDensityTilt_measurable (t : ℝ) {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hφm : Measurable φ) : Measurable (equilibriumDensityTilt t ρ φ) :=
  (measurable_const.add (measurable_const.mul hφm)).mul hρm

theorem equilibriumDensityTilt_nonneg {ρ φ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    {M t : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M)
    (ht : t ∈ Ioo (-(1 / (2 * (M + 1)))) (1 / (2 * (M + 1)))) (x : ℂ) :
    0 ≤ equilibriumDensityTilt t ρ φ x := by
  have hb := equilibrium_tilt_factor_bounds hM (hφM x) ht
  exact mul_nonneg (by linarith [hb.1]) (hρ0 x)

theorem equilibriumDensityTilt_integrable (t : ℝ) {ρ φ : ℂ → ℝ}
    (hρi : Integrable ρ) (hφm : Measurable φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M) :
    Integrable (equilibriumDensityTilt t ρ φ) := by
  have hi := hρi.mul_bdd hφm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hφM x))
  apply (hρi.add (hi.const_mul t)).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply, equilibriumDensityTilt]; ring)

/-- A zero mean under the actual reference law gives exact mass conservation. -/
theorem integral_equilibriumDensityTilt (t : ℝ) {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) (hφm : Measurable φ)
    {M : ℝ} (hφM : ∀ x, |φ x| ≤ M)
    (hφzero : (∫ x : ℂ, φ x ∂equilibriumDensityMeasure ρ) = 0) :
    (∫ x : ℂ, equilibriumDensityTilt t ρ φ x) = 1 := by
  have hi := hρi.mul_bdd hφm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hφM x))
  have he : equilibriumDensityTilt t ρ φ = (fun x => ρ x + t * (ρ x * φ x)) := by
    funext x
    unfold equilibriumDensityTilt
    ring
  rw [integral_equilibriumDensityMeasure hρm hρ0] at hφzero
  rw [he, integral_add hρi (hi.const_mul t), integral_const_mul, hρmass, hφzero]
  ring

theorem equilibriumDensityTilt_secondMoment_integrable (t : ℝ) {ρ φ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hφm : Measurable φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumDensityTilt t ρ φ x) := by
  have hi := hρ2.mul_bdd hφm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hφM x))
  apply (hρ2.add (hi.const_mul t)).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply, equilibriumDensityTilt]; ring)

theorem integral_equilibriumDensityTilt_secondMoment (t : ℝ) {ρ φ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hφm : Measurable φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M) :
    (∫ x : ℂ, ‖x‖ ^ 2 * equilibriumDensityTilt t ρ φ x) =
      (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) + t * (∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x) := by
  have hi := hρ2.mul_bdd hφm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hφM x))
  have he : (fun x : ℂ => ‖x‖ ^ 2 * equilibriumDensityTilt t ρ φ x) =
      (fun x => ‖x‖ ^ 2 * ρ x + t * ((‖x‖ ^ 2 * ρ x) * φ x)) := by
    funext x
    unfold equilibriumDensityTilt
    ring
  rw [he, integral_add hρ2 (hi.const_mul t), integral_const_mul]

theorem equilibrium_hasDerivAt_density_tilt_secondMoment {ρ φ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hφm : Measurable φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ x : ℂ, ‖x‖ ^ 2 * equilibriumDensityTilt t ρ φ x)
      (∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x) 0 := by
  have h : HasDerivAt (fun t : ℝ => (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) +
      t * (∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x))
      (∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x) 0 := by
    exact (hasDerivAt_mul_const (x := (0 : ℝ))
      (∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x)).const_add (∫ x : ℂ, ‖x‖ ^ 2 * ρ x)
  exact h.congr_of_eventuallyEq (Eventually.of_forall
    (fun t => integral_equilibriumDensityTilt_secondMoment t hρ2 hφm hφM))

/-- The complete physical free-energy first variation along an actual bounded
zero-mass tilt, with the manuscript's coefficients one-half, one-half, 1/beta. -/
theorem equilibrium_hasDerivAt_density_tilt_freeEnergy (β : ℝ) {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M)
    (hφzero : (∫ x : ℂ, φ x ∂equilibriumDensityMeasure ρ) = 0) :
    HasDerivAt (fun t : ℝ => equilibriumDensityFreeEnergy β (equilibriumDensityTilt t ρ φ))
      ((∫ x : ℂ, (‖x‖ ^ 2 * ρ x) * φ x) / 2 +
        (∫ x : ℂ, φ x * (equilibriumDensityPotential ρ x * ρ x)) +
        (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x) / β) 0 := by
  have hm := equilibrium_hasDerivAt_density_tilt_secondMoment hρ2 hφm hφM
  have hg := equilibrium_hasDerivAt_density_tilt_interaction hG hφm hM hφM
  have hh := equilibrium_hasDerivAt_zeroMass_density_tilt_entropy hρm hρ0 hρi hρmass hρH
    hφm hM hφM hφzero
  convert ((hm.div_const 2).add (hg.div_const 2)).add (hh.div_const β) using 1
  · rfl
  · ring

end RepulsiveCoulomb
