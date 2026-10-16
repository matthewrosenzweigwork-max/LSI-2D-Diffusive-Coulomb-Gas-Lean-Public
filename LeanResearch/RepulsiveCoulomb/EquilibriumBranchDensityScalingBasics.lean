module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityTiltAdmissible
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-! Literal normalized planar dilations and their exact entropy/moment laws.
The Jacobian is t^2, and the entropy shift is -2 log t. These inputs support
the manuscript virial identity directly from minimization, before any density
differentiability or radial regularity has been used. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumDensityScale (t : ℝ) (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  (t ^ 2)⁻¹ * ρ (t⁻¹ • x)

theorem equilibriumDensityScale_measurable (t : ℝ) {ρ : ℂ → ℝ} (hρm : Measurable ρ) :
    Measurable (equilibriumDensityScale t ρ) :=
  measurable_const.mul (hρm.comp (continuous_const_smul t⁻¹).measurable)

theorem equilibriumDensityScale_nonneg (t : ℝ) {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (x : ℂ) : 0 ≤ equilibriumDensityScale t ρ x :=
  mul_nonneg (inv_nonneg.mpr (sq_nonneg t)) (hρ0 _)

theorem equilibriumDensityScale_integrable {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρi : Integrable ρ) : Integrable (equilibriumDensityScale t ρ) :=
  (hρi.comp_smul (inv_ne_zero ht.ne')).const_mul _

theorem integral_equilibriumDensityScale {t : ℝ} (ht : 0 < t) (ρ : ℂ → ℝ) :
    (∫ x : ℂ, equilibriumDensityScale t ρ x) = ∫ x : ℂ, ρ x := by
  unfold equilibriumDensityScale
  rw [integral_const_mul, Measure.integral_comp_inv_smul (volume : Measure ℂ) ρ t]
  simp only [Complex.finrank_real_complex, abs_of_nonneg (sq_nonneg t), smul_eq_mul]
  field_simp [ht.ne']

theorem equilibriumDensityScale_secondMoment_integrand {t : ℝ} (ht : 0 < t)
    (ρ : ℂ → ℝ) (x : ℂ) :
    ‖x‖ ^ 2 * equilibriumDensityScale t ρ x = ‖t⁻¹ • x‖ ^ 2 * ρ (t⁻¹ • x) := by
  simp only [equilibriumDensityScale, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), mul_pow, inv_pow]
  ring

theorem equilibriumDensityScale_secondMoment_integrable {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * equilibriumDensityScale t ρ x) := by
  apply (hρ2.comp_smul (inv_ne_zero ht.ne')).congr
  exact Eventually.of_forall (fun x => (equilibriumDensityScale_secondMoment_integrand ht ρ x).symm)

theorem integral_equilibriumDensityScale_secondMoment {t : ℝ} (ht : 0 < t) (ρ : ℂ → ℝ) :
    (∫ x : ℂ, ‖x‖ ^ 2 * equilibriumDensityScale t ρ x) =
      t ^ 2 * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) := by
  simp_rw [equilibriumDensityScale_secondMoment_integrand ht ρ]
  rw [Measure.integral_comp_inv_smul (volume : Measure ℂ) (fun x : ℂ => ‖x‖ ^ 2 * ρ x) t]
  simp only [Complex.finrank_real_complex, abs_of_nonneg (sq_nonneg t), smul_eq_mul]

theorem equilibriumDensityScale_entropy_integrable {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x))) :
    Integrable (fun x : ℂ => equilibriumDensityScale t ρ x * Real.log (equilibriumDensityScale t ρ x)) := by
  have ht2 : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos ht)
  have h₁ := (hρH.comp_smul (inv_ne_zero ht.ne')).const_mul ((t ^ 2)⁻¹)
  have h₂ := (hρi.comp_smul (inv_ne_zero ht.ne')).const_mul ((t ^ 2)⁻¹ * Real.log ((t ^ 2)⁻¹))
  apply (h₁.add h₂).congr
  exact Eventually.of_forall (fun x => (equilibrium_mul_log_scale ht2 (hρ0 (t⁻¹ • x))).symm)

/-- The dimension-two entropy shift with exact normalization. -/
theorem integral_equilibriumDensityScale_entropy {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x))) :
    (∫ x : ℂ, equilibriumDensityScale t ρ x * Real.log (equilibriumDensityScale t ρ x)) =
      (∫ x : ℂ, ρ x * Real.log (ρ x)) - 2 * Real.log t := by
  have ht2 : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos ht)
  have h₁ := (hρH.comp_smul (inv_ne_zero ht.ne')).const_mul ((t ^ 2)⁻¹)
  have h₂ := (hρi.comp_smul (inv_ne_zero ht.ne')).const_mul ((t ^ 2)⁻¹ * Real.log ((t ^ 2)⁻¹))
  have he : (fun x : ℂ => equilibriumDensityScale t ρ x * Real.log (equilibriumDensityScale t ρ x)) =
      (fun x : ℂ => (t ^ 2)⁻¹ * (ρ (t⁻¹ • x) * Real.log (ρ (t⁻¹ • x))) +
        ((t ^ 2)⁻¹ * Real.log ((t ^ 2)⁻¹)) * ρ (t⁻¹ • x)) := by
    funext x
    exact equilibrium_mul_log_scale ht2 (hρ0 (t⁻¹ • x))
  rw [he, integral_add h₁ h₂, integral_const_mul, integral_const_mul,
    Measure.integral_comp_inv_smul (volume : Measure ℂ) (fun x : ℂ => ρ x * Real.log (ρ x)) t,
    Measure.integral_comp_inv_smul (volume : Measure ℂ) ρ t]
  simp only [Complex.finrank_real_complex, abs_of_nonneg (sq_nonneg t), smul_eq_mul,
    hρmass, mul_one, Real.log_inv, Real.log_pow]
  field_simp [ht.ne'] <;> ring

end RepulsiveCoulomb
