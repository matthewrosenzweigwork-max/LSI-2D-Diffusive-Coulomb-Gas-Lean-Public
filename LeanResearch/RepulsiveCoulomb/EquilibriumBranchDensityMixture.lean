module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFiniteDensityEnergy

@[expose] public section

/-! Actual finite-energy density mixtures and the exact quadratic Coulomb
expansion. No boundedness of the first density is assumed; the natural finite
cross-energy condition is supplied by the checked cross-interaction theorem
when the second density is the zero-set filling competitor. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumDensityMixture (ε : ℝ) (ρ ψ : ℂ → ℝ) (x : ℂ) : ℝ :=
  (1 - ε) * ρ x + ε * ψ x

def equilibriumDensityCrossIntegral (ρ ψ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2) ∂volume.prod volume

theorem equilibriumDensityMixture_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {ρ ψ : ℂ → ℝ} (hρ : ∀ x, 0 ≤ ρ x) (hψ : ∀ x, 0 ≤ ψ x) (x : ℂ) :
    0 ≤ equilibriumDensityMixture ε ρ ψ x :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr hε1) (hρ x)) (mul_nonneg hε0 (hψ x))

theorem equilibriumDensityMixture_measurable (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hρ : Measurable ρ) (hψ : Measurable ψ) : Measurable (equilibriumDensityMixture ε ρ ψ) :=
  (measurable_const.mul hρ).add (measurable_const.mul hψ)

theorem equilibriumDensityMixture_integrable (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hρ : Integrable ρ) (hψ : Integrable ψ) : Integrable (equilibriumDensityMixture ε ρ ψ) :=
  (hρ.const_mul (1 - ε)).add (hψ.const_mul ε)

theorem integral_equilibriumDensityMixture (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hρ : Integrable ρ) (hψ : Integrable ψ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) (hψmass : (∫ x : ℂ, ψ x) = 1) :
    (∫ x : ℂ, equilibriumDensityMixture ε ρ ψ x) = 1 := by
  unfold equilibriumDensityMixture
  rw [integral_add (hρ.const_mul (1 - ε)) (hψ.const_mul ε),
    integral_const_mul, integral_const_mul, hρmass, hψmass]
  ring

theorem equilibriumDensityCrossIntegral_symm (ρ ψ : ℂ → ℝ) :
    equilibriumDensityCrossIntegral ρ ψ = equilibriumDensityCrossIntegral ψ ρ := by
  unfold equilibriumDensityCrossIntegral
  calc
    _ = ∫ p : ℂ × ℂ, ρ p.2 * (equilibriumLogKernel (p.2 - p.1) * ψ p.1) ∂volume.prod volume :=
      (integral_prod_swap (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
        (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        change ρ p.2 * (equilibriumLogKernel (p.2 - p.1) * ψ p.1) =
          ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)
        rw [show equilibriumLogKernel (p.2 - p.1) = equilibriumLogKernel (p.1 - p.2) by
          simp only [equilibriumLogKernel, norm_sub_rev]]
        ring)

theorem equilibriumDensityCross_integrable_swap {ρ ψ : ℂ → ℝ}
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume)) :
    Integrable (fun p : ℂ × ℂ => ψ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume) := by
  apply hG.swap.congr
  exact Eventually.of_forall (fun p => by
    change ρ p.2 * (equilibriumLogKernel (p.2 - p.1) * ψ p.1) =
      ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)
    rw [show equilibriumLogKernel (p.2 - p.1) = equilibriumLogKernel (p.1 - p.2) by
      simp only [equilibriumLogKernel, norm_sub_rev]]
    ring)

private theorem equilibriumDensityMixture_pair_expand (ε : ℝ) (ρ ψ : ℂ → ℝ) (p : ℂ × ℂ) :
    equilibriumDensityMixture ε ρ ψ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityMixture ε ρ ψ p.2) =
    ((1 - ε) ^ 2 * (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) +
      ((1 - ε) * ε) * (ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) +
      ((1 - ε) * ε) * (ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2))) +
      ε ^ 2 * (ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) := by
  unfold equilibriumDensityMixture
  ring

theorem equilibriumDensityMixture_logEnergy_integrable (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hRR : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume))
    (hSS : Integrable (fun p : ℂ × ℂ => ψ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume)) :
    Integrable (fun p : ℂ × ℂ => equilibriumDensityMixture ε ρ ψ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityMixture ε ρ ψ p.2)) (volume.prod volume) := by
  have hSR := equilibriumDensityCross_integrable_swap hRS
  apply ((((hRR.const_mul ((1 - ε) ^ 2)).add (hRS.const_mul ((1 - ε) * ε))).add
    (hSR.const_mul ((1 - ε) * ε))).add (hSS.const_mul (ε ^ 2))).congr
  exact Eventually.of_forall (fun p => (equilibriumDensityMixture_pair_expand ε ρ ψ p).symm)

/-- The exact quadratic interaction formula, with every product-space
integrability obligation discharged before linearity/Fubini is used. -/
theorem equilibriumDensityMixture_interaction (ε : ℝ) {ρ ψ : ℂ → ℝ}
    (hRR : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hRS : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume))
    (hSS : Integrable (fun p : ℂ × ℂ => ψ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ψ p.2)) (volume.prod volume)) :
    equilibriumDensityInteraction (equilibriumDensityMixture ε ρ ψ) =
      (1 - ε) ^ 2 * equilibriumDensityInteraction ρ +
      2 * (1 - ε) * ε * equilibriumDensityCrossIntegral ρ ψ +
      ε ^ 2 * equilibriumDensityInteraction ψ := by
  have hSR := equilibriumDensityCross_integrable_swap hRS
  have h1 := integral_add (hRR.const_mul ((1 - ε) ^ 2)) (hRS.const_mul ((1 - ε) * ε))
  have h2 := integral_add ((hRR.const_mul ((1 - ε) ^ 2)).add (hRS.const_mul ((1 - ε) * ε)))
    (hSR.const_mul ((1 - ε) * ε))
  have h3 := integral_add (((hRR.const_mul ((1 - ε) ^ 2)).add (hRS.const_mul ((1 - ε) * ε))).add
    (hSR.const_mul ((1 - ε) * ε))) (hSS.const_mul (ε ^ 2))
  dsimp only [Pi.add_apply] at h1 h2 h3
  rw [equilibriumDensityInteraction_eq_product (equilibriumDensityMixture_logEnergy_integrable ε hRR hRS hSS)]
  simp_rw [equilibriumDensityMixture_pair_expand ε ρ ψ]
  rw [h3, h2, h1]
  simp only [integral_const_mul]
  change (1 - ε) ^ 2 * equilibriumDensityCrossIntegral ρ ρ +
    ((1 - ε) * ε) * equilibriumDensityCrossIntegral ρ ψ +
    ((1 - ε) * ε) * equilibriumDensityCrossIntegral ψ ρ +
    ε ^ 2 * equilibriumDensityCrossIntegral ψ ψ = _
  rw [equilibriumDensityCrossIntegral_symm ψ ρ]
  change (1 - ε) ^ 2 * (∫ p : ℂ × ℂ, ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2) ∂volume.prod volume) +
    ((1 - ε) * ε) * equilibriumDensityCrossIntegral ρ ψ +
    ((1 - ε) * ε) * equilibriumDensityCrossIntegral ρ ψ +
    ε ^ 2 * (∫ p : ℂ × ℂ, ψ p.1 * (equilibriumLogKernel (p.1 - p.2) * ψ p.2) ∂volume.prod volume) = _
  rw [← equilibriumDensityInteraction_eq_product hRR, ← equilibriumDensityInteraction_eq_product hSS]
  ring

end RepulsiveCoulomb
