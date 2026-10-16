import LeanResearch.RepulsiveCoulomb.EquilibriumBranchRadialMassFormula
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Global C1 and smoothness bootstrapping for the actual pointwise thermal
EL density. Newton's derivative includes the origin, and the exact mass
formula gives the Cartesian score with factor 1-2*pi*J. Compact convolution
then preserves C^n regularity of J, yielding all finite orders inductively. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology RealInnerProductSpace
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumScoreDerivative (β : ℝ) (ρ : ℂ → ℝ) (x : ℂ) : ℂ →L[ℝ] ℝ :=
  (-β * (1 - 2 * Real.pi * equilibriumRadialAverage ρ x) * ρ x) • innerSL ℝ x

theorem equilibriumNewtonDerivative_eq_radialAverage {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) (x : ℂ) :
    equilibriumNewtonDerivative (equilibriumDensityMeasure ρ) x =
      (-2 * Real.pi * equilibriumRadialAverage ρ x) • innerSL ℝ x := by
  by_cases hx : x = 0
  · subst x
    simp only [equilibriumNewtonDerivative_zero, map_zero, smul_zero]
  · unfold equilibriumNewtonDerivative
    rw [equilibriumCumulativeMass_eq_radialAverage hρm hρ0 hρrad]
    congr 1
    field_simp [norm_ne_zero_iff.mpr hx] <;> ring

theorem equilibrium_pointwise_EL_density_eq_exp {β C : ℝ} {ρ : ℂ → ℝ}
    (hρpos : ∀ x, 0 < ρ x)
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (x : ℂ) :
    ρ x = Real.exp (-β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) := by
  rw [← hEL x, Real.exp_log (hρpos x)]

/-- C1 regularity is obtained from bounded measurable radial data and EL,
not used as an input to the Newton differentiation step. -/
theorem equilibrium_pointwise_EL_contDiff_one {β C M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) :
    ContDiff ℝ 1 ρ := by
  have hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ →
      equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y := by
    intro x y hxy
    exact equilibriumDensityPotential_radial_of_EL hβ hρrad hEL hxy
  have hU := equilibriumDensityPotential_contDiff_one hρm (fun x => (hρpos x).le) hρM hρi hρmass hρ2 hUrad
  have h : ContDiff ℝ 1 (fun x : ℂ => Real.exp (-β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)) :=
    ((contDiff_const.mul (((contDiff_norm_sq (𝕜 := ℝ)).div_const 2).add hU)).add contDiff_const).exp
  have he := funext (equilibrium_pointwise_EL_density_eq_exp hρpos hEL)
  rwa [← he] at h

/-- The exact Cartesian first derivative, with the sharp normalization factor
2*pi and with the origin covered by the Newton origin proof. -/
theorem equilibrium_pointwise_EL_hasFDerivAt_score {β C M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (x : ℂ) : HasFDerivAt ρ (equilibriumScoreDerivative β ρ x) x := by
  have hρ0 := fun y => (hρpos y).le
  have hUrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ →
      equilibriumDensityPotential ρ x = equilibriumDensityPotential ρ y := by
    intro x y hxy
    exact equilibriumDensityPotential_radial_of_EL hβ hρrad hEL hxy
  have hU := equilibriumDensityPotential_hasFDerivAt_newton hρm hρ0 hρM hρi hρmass hρ2 hUrad x
  rw [equilibriumNewtonDerivative_eq_radialAverage hρm hρ0 hρrad x] at hU
  have hV : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2 / 2 + equilibriumDensityPotential ρ y)
      ((1 - 2 * Real.pi * equilibriumRadialAverage ρ x) • innerSL ℝ x) x := by
    convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)).add hU using 1
    · funext y
      simp only [Pi.add_apply] <;> ring
    · ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
  have hd := ((hV.const_mul (-β)).add_const C).exp
  have hde := hd.congr_of_eventuallyEq
    (Eventually.of_forall (equilibrium_pointwise_EL_density_eq_exp hρpos hEL))
  convert hde using 1
  rw [← equilibrium_pointwise_EL_density_eq_exp hρpos hEL x]
  ext v
  simp only [equilibriumScoreDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The preceding genuine score identity and compact-convolution radial
average give smoothness by induction over every finite derivative order. -/
theorem equilibrium_pointwise_EL_contDiff {β C M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y)
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := by
  have hC1 := equilibrium_pointwise_EL_contDiff_one hβ hρm hρpos hρM hρi hρmass hρ2 hρrad hEL
  have hscore := equilibrium_pointwise_EL_hasFDerivAt_score hβ hρm hρpos hρM hρi hρmass hρ2 hρrad hEL
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hC1.continuous
  | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨equilibriumScoreDerivative β ρ, ?_, hscore⟩
      have hJ := equilibriumRadialAverage_contDiff (n := (n : ℕ∞)) ih
      have hcoef : ContDiff ℝ n (fun x : ℂ => -β * (1 - 2 * Real.pi * equilibriumRadialAverage ρ x) * ρ x) :=
        (contDiff_const.mul (contDiff_const.sub (contDiff_const.mul hJ))).mul ih
      exact hcoef.smul (innerSL ℝ).contDiff

/-- Smooth radial positive equilibrium densities are actually constructed for
every beta>0. The sharp cap and higher-order quantitative tails are separate
remaining conclusions, not inputs here. -/
theorem equilibrium_exists_smooth_radial_EL_minimizer {β : ℝ} (hβ : 0 < β) :
    ∃ (μ : ProbabilityMeasure ℂ) (ρ : ℂ → ℝ) (C M : ℝ),
      equilibriumNonnegativeObjective β μ ≠ ∞ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      (∀ x, 0 < ρ x) ∧ 0 < M ∧ (∀ x, ρ x ≤ M) ∧
      Integrable ρ ∧ (∫ x : ℂ, ρ x) = 1 ∧
      Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x) ∧
      equilibriumDensityMeasure ρ = (μ : Measure ℂ) ∧
      (∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y) ∧
      (∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) ∧
      ∀ ν : ProbabilityMeasure ℂ,
        equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν := by
  obtain ⟨μ, ρ, C, M, hfinite, hρm, hρpos, hM, hρM, hρi, hρmass, hρ2, hρH, hρμ, hEL, hmin⟩ :=
    equilibrium_exists_bounded_EL_minimizer hβ
  have hρL := equilibriumLogMoment_mul_integrable hρm (fun x => (hρpos x).le) hρi hρ2
  have hrad : ∀ ⦃x y : ℂ⦄, ‖x‖ = ‖y‖ → ρ x = ρ y := by
    intro x y hxy
    exact equilibrium_pointwise_EL_radial hβ hρm hρpos hρM hρi hρmass hρL hEL hxy
  have hsmooth := equilibrium_pointwise_EL_contDiff hβ hρm hρpos hρM hρi hρmass hρ2 hrad hEL
  exact ⟨μ, ρ, C, M, hfinite, hsmooth, hρpos, hM, hρM, hρi, hρmass, hρ2, hρμ, hrad, hEL, hmin⟩

end RepulsiveCoulomb
