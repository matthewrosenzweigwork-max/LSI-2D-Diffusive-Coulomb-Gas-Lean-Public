module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPotential

@[expose] public section

/-! Interaction integrability and quantitative energy bounds for actual
bounded planar probability densities. These bounds retain the logarithmic
moment explicitly, so compact-temperature control is not hidden. -/
noncomputable section
open MeasureTheory Set Real Filter
namespace RepulsiveCoulomb

/-- The literal iterated Coulomb interaction integral. -/
def equilibriumDensityInteraction (ρ : ℂ → ℝ) : ℝ :=
  ∫ x : ℂ, equilibriumDensityPotential ρ x * ρ x

theorem equilibriumDensityPotential_abs_bound {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y)) (x : ℂ) :
    |equilibriumDensityPotential ρ x| ≤ M * Real.pi / 2 + equilibriumLogMoment x +
      (∫ y : ℂ, equilibriumLogMoment y * ρ y) := by
  have hl := equilibriumDensityPotential_lower hρm hρ0 hρM hρi hρmass hρL x
  have hu := equilibriumDensityPotential_upper hρm hρ0 hρM hρi hρL x
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have hp : 0 ≤ M * Real.pi / 2 := by positivity
  have hx := equilibriumLogMoment_nonneg x
  have hL : 0 ≤ ∫ y : ℂ, equilibriumLogMoment y * ρ y :=
    integral_nonneg (fun y => mul_nonneg (equilibriumLogMoment_nonneg y) (hρ0 y))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem equilibriumDensityInteraction_integrable {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y)) :
    Integrable (fun x : ℂ => equilibriumDensityPotential ρ x * ρ x) := by
  let L := ∫ y : ℂ, equilibriumLogMoment y * ρ y
  have hi := ((hρi.const_mul (M * Real.pi / 2)).add hρL).add (hρi.const_mul L)
  apply hi.mono' ((equilibriumDensityPotential_measurable hρm).mul hρm).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    dsimp only [Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
    have h := mul_le_mul_of_nonneg_right
      (equilibriumDensityPotential_abs_bound hρm hρ0 hρM hρi hρmass hρL x) (hρ0 x)
    dsimp only [L]
    nlinarith)

theorem equilibriumDensityInteraction_lower {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y)) :
    -2 * (∫ y : ℂ, equilibriumLogMoment y * ρ y) ≤ equilibriumDensityInteraction ρ := by
  let L := ∫ y : ℂ, equilibriumLogMoment y * ρ y
  have hi := hρL.neg.sub (hρi.const_mul L)
  have hm := integral_mono hi
    (equilibriumDensityInteraction_integrable hρm hρ0 hρM hρi hρmass hρL)
    (fun x => show -(equilibriumLogMoment x * ρ x) - L * ρ x ≤
        equilibriumDensityPotential ρ x * ρ x by
      have h := mul_le_mul_of_nonneg_right
        (equilibriumDensityPotential_lower hρm hρ0 hρM hρi hρmass hρL x) (hρ0 x)
      dsimp only [L]
      nlinarith)
  change (∫ x : ℂ, -(equilibriumLogMoment x * ρ x) - L * ρ x) ≤
    equilibriumDensityInteraction ρ at hm
  have hsub := integral_sub hρL.neg (hρi.const_mul L)
  dsimp only [Pi.neg_apply] at hsub
  rw [hsub, integral_neg, integral_const_mul, hρmass, mul_one] at hm
  dsimp only [L] at hm
  linarith

theorem equilibriumDensityInteraction_upper {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y)) :
    equilibriumDensityInteraction ρ ≤ M * Real.pi / 2 := by
  have hm := integral_mono
    (equilibriumDensityInteraction_integrable hρm hρ0 hρM hρi hρmass hρL)
    (hρi.const_mul (M * Real.pi / 2))
    (fun x => mul_le_mul_of_nonneg_right
      (equilibriumDensityPotential_upper hρm hρ0 hρM hρi hρL x) (hρ0 x))
  simpa only [integral_const_mul, hρmass, mul_one, equilibriumDensityInteraction] using hm


/-- Quantitative logarithmic-moment absorption after integration. -/
theorem equilibriumLogMoment_integral_le_quadratic {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    (∫ x : ℂ, equilibriumLogMoment x * ρ x) ≤
      δ * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) + (4 * δ)⁻¹ := by
  have hl := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hi := (hρ2.const_mul δ).add (hρi.const_mul ((4 * δ)⁻¹))
  have hm := integral_mono hl hi (fun x =>
    show equilibriumLogMoment x * ρ x ≤ δ * (‖x‖ ^ 2 * ρ x) + (4 * δ)⁻¹ * ρ x by
      have h := mul_le_mul_of_nonneg_right (equilibriumLogMoment_le_quadratic hδ x) (hρ0 x)
      nlinarith)
  change (∫ x : ℂ, equilibriumLogMoment x * ρ x) ≤
      ∫ x : ℂ, δ * (‖x‖ ^ 2 * ρ x) + (4 * δ)⁻¹ * ρ x at hm
  rw [integral_add (hρ2.const_mul δ) (hρi.const_mul _), integral_const_mul,
    integral_const_mul, hρmass, mul_one] at hm
  exact hm

end RepulsiveCoulomb
