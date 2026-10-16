module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialWeakRegularity
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchRadialMassFormula
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! An actual smooth bootstrap starting from
supplied C1 regularity of the literal potential, with a raw-input wrapper
discharging that premise from the NEW weak regularity producer. It does not
call equilibrium_pointwise_EL_contDiff or an old selected thermal reference.
The only reused radial tools are the literal mass formula and the generic
Cn-preservation theorem for the radial averaging operator. -/
noncomputable section
open MeasureTheory Real Filter InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace
namespace RepulsiveCoulomb.PaperRoute

theorem thermal_radial_EL_smooth_of_potential_contDiff_one
    {ρ : ℂ → ℝ} {β C M : ℝ} (hβ : 0 < β)
    (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2*ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ → ρ x=ρ y)
    (hEL : ∀ x, Real.log (ρ x) =
      -β*(‖x‖^2/2+equilibriumDensityPotential ρ x)+C)
    (hU1 : ContDiff ℝ 1 (equilibriumDensityPotential ρ)) :
    ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ) := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρpos x).le
  have hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ →
      equilibriumDensityPotential ρ x=equilibriumDensityPotential ρ y := by
    intro x y hxy
    have h := congrArg Real.log (hρrad hxy)
    rw [hEL x, hEL y, hxy] at h
    apply mul_left_cancel₀ hβ.ne'
    linarith
  have hρexp (x : ℂ) : ρ x =
      Real.exp (-β*(‖x‖^2/2+equilibriumDensityPotential ρ x)+C) := by
    rw [← hEL x, Real.exp_log (hρpos x)]
  /- The supplied/new C1(U) is ACTUALLY consumed here. -/
  have hρ1 : ContDiff ℝ 1 ρ := by
    have h : ContDiff ℝ 1 (fun x : ℂ =>
        Real.exp (-β*(‖x‖^2/2+equilibriumDensityPotential ρ x)+C)) :=
      ((contDiff_const.mul (((contDiff_norm_sq (𝕜 := ℝ)).div_const 2).add hU1)).add contDiff_const).exp
    rwa [← funext hρexp] at h
  have hDU (x : ℂ) : HasFDerivAt (equilibriumDensityPotential ρ)
      ((-2*Real.pi*equilibriumRadialAverage ρ x) • innerSL ℝ x) x := by
    have hd := (hU1.differentiable (by norm_num) x).hasFDerivAt
    have he : fderiv ℝ (equilibriumDensityPotential ρ) x =
        (-2*Real.pi*equilibriumRadialAverage ρ x) • innerSL ℝ x := by
      rw [thermalDensityPotential_fderiv_eq_newtonGradient hρm hρ0 hρM hρi hρmass hρ2 hUrad,
        thermalNewtonGradient_riesz]
      by_cases hx : x = 0
      · subst x
        simp only [equilibriumNewtonDerivative_zero, map_zero, smul_zero]
      · unfold equilibriumNewtonDerivative
        rw [equilibriumCumulativeMass_eq_radialAverage hρm hρ0 hρrad]
        congr 1
        field_simp [norm_ne_zero_iff.mpr hx]
    rwa [he] at hd
  let S : ℂ → ℂ →L[ℝ] ℝ := fun x =>
    (-β*(1-2*Real.pi*equilibriumRadialAverage ρ x)*ρ x) • innerSL ℝ x
  have hscore (x : ℂ) : HasFDerivAt ρ (S x) x := by
    have hV : HasFDerivAt (fun y : ℂ => ‖y‖^2/2+equilibriumDensityPotential ρ y)
        ((1-2*Real.pi*equilibriumRadialAverage ρ x) • innerSL ℝ x) x := by
      convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1/2 : ℝ)).add (hDU x) using 1
      · funext y
        simp only [Pi.add_apply]
        ring
      · ext v
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
    have hd := ((hV.const_mul (-β)).add_const C).exp
    have hde := hd.congr_of_eventuallyEq (Eventually.of_forall hρexp)
    convert hde using 1
    rw [← hρexp x]
    ext v
    simp only [S, smul_apply, smul_eq_mul]
    ring
  have hρsmooth : ContDiff ℝ (⊤ : ℕ∞) ρ := by
    apply contDiff_infty.mpr
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr hρ1.continuous
    | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨S, ?_, hscore⟩
      have hJ := equilibriumRadialAverage_contDiff (n := (n : ℕ∞)) ih
      have hc : ContDiff ℝ n (fun x : ℂ =>
          -β*(1-2*Real.pi*equilibriumRadialAverage ρ x)*ρ x) :=
        (contDiff_const.mul (contDiff_const.sub (contDiff_const.mul hJ))).mul ih
      exact hc.smul (innerSL ℝ).contDiff
  refine ⟨hρsmooth, ?_⟩
  apply contDiff_infty.mpr
  intro n
  cases n with
  | zero => exact contDiff_zero.mpr hU1.continuous
  | succ n =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => (-2*Real.pi*equilibriumRadialAverage ρ x) • innerSL ℝ x, ?_, hDU⟩
    have hρn : ContDiff ℝ n ρ := hρsmooth.of_le (by simp)
    have hJ := equilibriumRadialAverage_contDiff (n := (n : ℕ∞)) hρn
    have hc : ContDiff ℝ n (fun x : ℂ => -2*Real.pi*equilibriumRadialAverage ρ x) :=
      contDiff_const.mul hJ
    exact hc.smul (innerSL ℝ).contDiff

/-- Original raw-density input: the NEW weak regularity bundle supplies the
load-bearing C1(U) premise before the exponential EL bootstrap is applied. -/
theorem thermal_radial_EL_smooth
    {ρ : ℂ → ℝ} {β C M : ℝ} (hβ : 0 < β)
    (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2*ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ → ρ x=ρ y)
    (hEL : ∀ x, Real.log (ρ x) =
      -β*(‖x‖^2/2+equilibriumDensityPotential ρ x)+C) :
    ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ) := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρpos x).le
  have hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖=‖y‖ →
      equilibriumDensityPotential ρ x=equilibriumDensityPotential ρ y := by
    intro x y hxy
    have h := congrArg Real.log (hρrad hxy)
    rw [hEL x, hEL y, hxy] at h
    apply mul_left_cancel₀ hβ.ne'
    linarith
  have hreg := thermal_radial_weak_regularity hρm hρ0 hρM hρi hρmass hρ2 hUrad
  exact thermal_radial_EL_smooth_of_potential_contDiff_one hβ hρm hρpos hρM
    hρi hρmass hρ2 hρrad hEL hreg.1

end RepulsiveCoulomb.PaperRoute
