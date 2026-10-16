module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFiniteDensityEnergy
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityTiltEntropy

@[expose] public section

/-! Actual finite logarithmic interaction under a bounded multiplicative tilt.
Every linear and quadratic product-space integrand is integrable, and the
quadratic expansion and first variation use the actual mean-field potential.
No regularity or boundedness of the base density is assumed. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumDensityTilt (t : ℝ) (ρ φ : ℂ → ℝ) (x : ℂ) : ℝ :=
  (1 + t * φ x) * ρ x

def equilibriumDensityTiltLinear (ρ φ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, φ p.1 * (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) ∂volume.prod volume

def equilibriumDensityTiltQuadratic (ρ φ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, (φ p.1 * φ p.2) *
    (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) ∂volume.prod volume

/-- Bounded tilts preserve actual absolute product-space energy integrability. -/
theorem equilibriumDensityTilt_logEnergy_integrable (t : ℝ) {ρ φ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) :
    Integrable (fun p : ℂ × ℂ => equilibriumDensityTilt t ρ φ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityTilt t ρ φ p.2)) (volume.prod volume) := by
  have h₁ := hG.bdd_mul (hφm.comp measurable_fst).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.1))
  have h₂ := hG.bdd_mul (hφm.comp measurable_snd).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.2))
  have h₃ := h₁.bdd_mul (hφm.comp measurable_snd).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.2))
  apply (((hG.add (h₁.const_mul t)).add (h₂.const_mul t)).add (h₃.const_mul (t ^ 2))).congr
  exact Eventually.of_forall (fun p => by
    dsimp only [Pi.add_apply, equilibriumDensityTilt, Function.comp_apply]
    ring)

/-- The two linear interaction terms are equal by the actual product swap. -/
theorem equilibriumDensityTiltLinear_swap (ρ φ : ℂ → ℝ) :
    (∫ p : ℂ × ℂ, φ p.2 *
      (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) ∂volume.prod volume) =
        equilibriumDensityTiltLinear ρ φ := by
  calc
    _ = ∫ p : ℂ × ℂ, φ p.1 *
      (ρ p.2 * (equilibriumLogKernel (p.2 - p.1) * ρ p.1)) ∂volume.prod volume :=
      (integral_prod_swap (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
        (fun p : ℂ × ℂ => φ p.2 *
          (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)))).symm
    _ = _ := by
      unfold equilibriumDensityTiltLinear
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [equilibriumLogKernel, norm_sub_rev]
        ring)

/-- Exact logarithmic interaction expansion for every real tilt parameter. -/
theorem equilibriumDensityTilt_interaction (t : ℝ) {ρ φ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) :
    equilibriumDensityInteraction (equilibriumDensityTilt t ρ φ) =
      equilibriumDensityInteraction ρ + 2 * t * equilibriumDensityTiltLinear ρ φ +
        t ^ 2 * equilibriumDensityTiltQuadratic ρ φ := by
  have h₁ := hG.bdd_mul (hφm.comp measurable_fst).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.1))
  have h₂ := hG.bdd_mul (hφm.comp measurable_snd).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.2))
  have h₃' := h₁.bdd_mul (hφm.comp measurable_snd).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.2))
  have h₃ : Integrable (fun p : ℂ × ℂ => (φ p.1 * φ p.2) *
      (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2))) (volume.prod volume) := by
    apply h₃'.congr
    exact Eventually.of_forall (fun p => by dsimp only [Function.comp_apply]; ring)
  have he : (fun p : ℂ × ℂ => equilibriumDensityTilt t ρ φ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityTilt t ρ φ p.2)) =
      (fun p : ℂ × ℂ => ((ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2) +
        t * (φ p.1 * (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)))) +
        t * (φ p.2 * (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)))) +
        t ^ 2 * ((φ p.1 * φ p.2) * (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)))) := by
    funext p
    unfold equilibriumDensityTilt
    ring
  have hi₁ := integral_add hG (h₁.const_mul t)
  have hi₂ := integral_add (hG.add (h₁.const_mul t)) (h₂.const_mul t)
  have hi₃ := integral_add ((hG.add (h₁.const_mul t)).add (h₂.const_mul t)) (h₃.const_mul (t ^ 2))
  dsimp only [Pi.add_apply, Function.comp_apply] at hi₁ hi₂ hi₃
  rw [equilibriumDensityInteraction_eq_product (equilibriumDensityTilt_logEnergy_integrable t hG hφm hM hφM),
    he, hi₃, hi₂, hi₁]
  simp only [integral_const_mul]
  rw [← equilibriumDensityInteraction_eq_product hG, equilibriumDensityTiltLinear_swap]
  change equilibriumDensityInteraction ρ + t * equilibriumDensityTiltLinear ρ φ +
    t * equilibriumDensityTiltLinear ρ φ + t ^ 2 * equilibriumDensityTiltQuadratic ρ φ = _
  ring

/-- The linear coefficient is the actual density-weighted mean-field potential,
with Fubini justified by absolute product energy integrability. -/
theorem equilibriumDensityTiltLinear_eq_potential {ρ φ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hφm : Measurable φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M) :
    equilibriumDensityTiltLinear ρ φ =
      ∫ x : ℂ, φ x * (equilibriumDensityPotential ρ x * ρ x) := by
  have h₁ := hG.bdd_mul (hφm.comp measurable_fst).aestronglyMeasurable
    (Eventually.of_forall (fun p : ℂ × ℂ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hφM p.1))
  dsimp only [Function.comp_apply] at h₁
  unfold equilibriumDensityTiltLinear
  rw [integral_prod _ h₁]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [integral_const_mul, integral_const_mul]
    unfold equilibriumDensityPotential
    ring)

/-- The interaction first variation, without density regularity assumptions. -/
theorem equilibrium_hasDerivAt_density_tilt_interaction {ρ φ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) :
    HasDerivAt (fun t : ℝ => equilibriumDensityInteraction (equilibriumDensityTilt t ρ φ))
      (2 * (∫ x : ℂ, φ x * (equilibriumDensityPotential ρ x * ρ x))) 0 := by
  have hp : HasDerivAt (fun t : ℝ => equilibriumDensityInteraction ρ +
      2 * t * equilibriumDensityTiltLinear ρ φ + t ^ 2 * equilibriumDensityTiltQuadratic ρ φ)
      (2 * equilibriumDensityTiltLinear ρ φ) 0 := by
    have hd := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (equilibriumDensityTiltLinear ρ φ)).const_add (equilibriumDensityInteraction ρ)).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (equilibriumDensityTiltQuadratic ρ φ))
    change HasDerivAt (fun t : ℝ => equilibriumDensityInteraction ρ +
      2 * t * equilibriumDensityTiltLinear ρ φ + t ^ 2 * equilibriumDensityTiltQuadratic ρ φ) _ 0 at hd
    simpa using hd
  have hactual := hp.congr_of_eventuallyEq
    (Eventually.of_forall (fun t => equilibriumDensityTilt_interaction t hG hφm hM hφM))
  rwa [equilibriumDensityTiltLinear_eq_potential hG hφm hφM] at hactual

end RepulsiveCoulomb
