import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialELBootstrap
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual real-axis profiles and enclosed mass. The potential derivative is obtained
from the actual Newton derivative of the literal convolution. No old all-order
thermal tail theorem is used. All identities differentiated later hold on Ioi 0;
the real-axis density and potential profiles themselves are globally smooth. -/
noncomputable section
open MeasureTheory Real Set Filter InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace
namespace RepulsiveCoulomb.PaperRoute

def thermalDensityProfile (ρ : ℂ → ℝ) (r : ℝ) : ℝ := ρ (r : ℂ)
def thermalPotentialProfile (ρ : ℂ → ℝ) (r : ℝ) : ℝ :=
  equilibriumDensityPotential ρ (r : ℂ)
def thermalMassProfile (q : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * Real.pi * ∫ s in (0 : ℝ)..r, s * q s
def thermalConfinementProfile (u : ℝ → ℝ) (r : ℝ) : ℝ := r ^ 2 / 2 + u r

theorem thermalDensityProfile_contDiff {ρ : ℂ → ℝ} {n : ℕ∞}
    (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (thermalDensityProfile ρ) :=
  hρ.comp Complex.ofRealCLM.contDiff

theorem thermalPotentialProfile_contDiff {ρ : ℂ → ℝ} {n : ℕ∞}
    (hU : ContDiff ℝ n (equilibriumDensityPotential ρ)) :
    ContDiff ℝ n (thermalPotentialProfile ρ) :=
  hU.comp Complex.ofRealCLM.contDiff

theorem thermalConfinementProfile_contDiff {u : ℝ → ℝ} {n : ℕ∞}
    (hu : ContDiff ℝ n u) : ContDiff ℝ n (thermalConfinementProfile u) :=
  ((contDiff_id.pow 2).div_const 2).add hu

theorem thermalMassProfile_hasDerivAt {q : ℝ → ℝ} (hq : Continuous q) (r : ℝ) :
    HasDerivAt (thermalMassProfile q) (2 * Real.pi * (r * q r)) r := by
  have hc : Continuous (fun s : ℝ => s * q s) := continuous_id.mul hq
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul _

theorem thermalMassProfile_deriv {q : ℝ → ℝ} (hq : Continuous q) :
    deriv (thermalMassProfile q) = fun r => 2 * Real.pi * (r * q r) :=
  funext fun r => (thermalMassProfile_hasDerivAt hq r).deriv

theorem thermalMassProfile_contDiff {q : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (thermalMassProfile q) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (thermalMassProfile_hasDerivAt hq.continuous r).differentiableAt, ?_⟩
  rw [thermalMassProfile_deriv hq.continuous]
  exact contDiff_const.mul (contDiff_id.mul hq)

theorem thermalMassProfile_eq_cumulative {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    {r : ℝ} (hr : 0 ≤ r) :
    thermalMassProfile (thermalDensityProfile ρ) r =
      equilibriumCumulativeMass (equilibriumDensityMeasure ρ) r := by
  exact (equilibriumCumulativeMass_radial_profile hρm hρ0 hρrad hr).symm

theorem thermalMassProfile_mem_unitInterval {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ thermalMassProfile (thermalDensityProfile ρ) r ∧
      thermalMassProfile (thermalDensityProfile ρ) r ≤ 1 := by
  let := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  rw [thermalMassProfile_eq_cumulative hρm hρ0 hρrad hr]
  exact ⟨equilibriumCumulativeMass_nonneg _ _, measureReal_le_one⟩

/-- Actual Newton derivative restricted to the positive real ray. -/
theorem thermalPotentialProfile_hasDerivAt {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ →
      equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (thermalPotentialProfile ρ)
      (-thermalMassProfile (thermalDensityProfile ρ) r / r) r := by
  have hd := (equilibriumDensityPotential_hasFDerivAt_newton
    hρm hρ0 hρM hρi hρmass hρ2 hUrad (r : ℂ)).comp_hasDerivAt r
      Complex.ofRealCLM.hasDerivAt
  have hi : inner ℝ (r : ℂ) (1 : ℂ) = r := by
    have he : (r : ℂ) = r • (1 : ℂ) := by simp
    rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  have hn : ‖(r : ℂ)‖ = r := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  convert hd using 1
  · rfl
  · simp only [equilibriumNewtonDerivative, smul_apply,
      smul_eq_mul, innerSL_apply_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
      hn, hi]
    rw [thermalMassProfile_eq_cumulative hρm hρ0 hρrad hr.le]
    field_simp

/-- The multiplied identity is the convenient route-faithful form for repeated
Leibniz differentiation. It is asserted only on the punctured positive ray. -/
theorem thermalPotentialProfile_mul_deriv {ρ : ℂ → ℝ} {M : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ →
      equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y) :
    EqOn (fun r => r * deriv (thermalPotentialProfile ρ) r)
      (fun r => -thermalMassProfile (thermalDensityProfile ρ) r) (Ioi 0) := by
  intro r hr
  change 0 < r at hr
  change r * deriv (thermalPotentialProfile ρ) r = -thermalMassProfile (thermalDensityProfile ρ) r
  rw [(thermalPotentialProfile_hasDerivAt hρm hρ0 hρM hρi hρmass hρ2 hρrad hUrad hr).deriv]
  field_simp [ne_of_gt hr]

theorem thermalDensityProfile_eq_exp {ρ : ℂ → ℝ} {β C : ℝ}
    (hρpos : ∀ x, 0 < ρ x)
    (hEL : ∀ x, Real.log (ρ x) =
      -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) (r : ℝ) :
    thermalDensityProfile ρ r =
      Real.exp (-β * thermalConfinementProfile (thermalPotentialProfile ρ) r + C) := by
  have h := hEL (r : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [thermalDensityProfile, ← Real.exp_log (hρpos (r : ℂ)), h]
  rfl

/-- Differentiate the actual exponential EL identity, on every real radius. -/
theorem thermalDensityProfile_deriv_score {ρ : ℂ → ℝ} {β C : ℝ}
    (hρpos : ∀ x, 0 < ρ x)
    (hEL : ∀ x, Real.log (ρ x) =
      -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (hU : ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ)) :
    deriv (thermalDensityProfile ρ) = fun r =>
      -β * deriv (thermalConfinementProfile (thermalPotentialProfile ρ)) r *
        thermalDensityProfile ρ r := by
  let W := thermalConfinementProfile (thermalPotentialProfile ρ)
  have hW : ContDiff ℝ (⊤ : ℕ∞) W :=
    thermalConfinementProfile_contDiff (thermalPotentialProfile_contDiff hU)
  funext r
  have hd := (((hW.differentiable (by simp) r).hasDerivAt.const_mul (-β)).add_const C).exp
  have he : thermalDensityProfile ρ = fun r => Real.exp (-β * W r + C) :=
    funext (thermalDensityProfile_eq_exp hρpos hEL)
  rw [he]
  rw [hd.deriv]
  ring

end RepulsiveCoulomb.PaperRoute
