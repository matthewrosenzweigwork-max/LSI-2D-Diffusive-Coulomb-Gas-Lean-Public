import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalBoundedPoisson
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalRadialELBootstrap
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalLaplacianMaximum
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchELTailBound
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-! The original Laplacian-at-maximum proof
of the sharp density cap. Actual weak Poisson is upgraded to classical
Poisson through test-function uniqueness and C2 regularity. No old circle-
average cap, old thermal smoothness producer, or selected reference is used. -/
noncomputable section
open MeasureTheory Real Set Filter Metric InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace
namespace RepulsiveCoulomb.PaperRoute

/-- NEW weak Poisson plus actual C2 regularity gives the classical equation
pointwise, not merely a formal or a.e. Laplacian. -/
theorem boundedDensityPotential_classical_poisson {ρ : ℂ → ℝ} {M : ℝ}
    (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2*ρ x))
    (hU2 : ContDiff ℝ 2 (equilibriumDensityPotential ρ)) (x : ℂ) :
    Laplacian.laplacian (equilibriumDensityPotential ρ) x = (-2*Real.pi)*ρ x := by
  have hL : Continuous (Laplacian.laplacian (equilibriumDensityPotential ρ)) :=
    continuous_laplacian_of_contDiff_two hU2
  have hR : Continuous (fun x : ℂ => (-2*Real.pi)*ρ x) := continuous_const.mul hρc
  have hae : Laplacian.laplacian (equilibriumDensityPotential ρ) =ᵐ[volume]
      (fun x => (-2*Real.pi)*ρ x) := by
    apply ae_eq_of_integral_contDiff_smul_eq hL.locallyIntegrable hR.locallyIntegrable
    intro φ hφ hφc
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
    have hw := boundedDensityPotential_weak_poisson hρc.measurable hρ0 hρM
      hρi hρmass hρ2 hφ2 hφc
    have hibp := integral_mul_laplacian_eq hU2 hφ2 hφc
    change (∫ y : ℂ, φ y*Laplacian.laplacian (equilibriumDensityPotential ρ) y) =
      ∫ y : ℂ, φ y*((-2*Real.pi)*ρ y)
    calc
      (∫ y : ℂ, φ y*Laplacian.laplacian (equilibriumDensityPotential ρ) y) =
          ∫ y : ℂ, Laplacian.laplacian (equilibriumDensityPotential ρ) y*φ y := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => mul_comm _ _
      _ = ∫ y : ℂ, equilibriumDensityPotential ρ y*Laplacian.laplacian φ y := hibp.symm
      _ = (-2*Real.pi)*(∫ y : ℂ, ρ y*φ y) := hw.2.2
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by ring
  exact congrFun (Measure.eq_of_ae_eq hae hL hR) x

theorem thermal_complex_laplacian_norm_sq (z : ℂ) :
    Laplacian.laplacian (fun x : ℂ => ‖x‖^2) z = 4 := by
  have hfirst : fderiv ℝ (fun w : ℂ => ‖w‖^2) =
      (fun w => innerSL ℝ w + innerSL ℝ w) := by
    funext w
    simp only [fderiv_norm_sq_apply, two_smul]
  have hd (x : ℂ) : fderiv ℝ (fderiv ℝ (fun w : ℂ => ‖w‖^2)) x =
      innerSL ℝ + innerSL ℝ := by
    rw [hfirst]
    exact ((innerSL ℝ (E := ℂ)).hasFDerivAt.add (innerSL ℝ (E := ℂ)).hasFDerivAt).fderiv
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, hd]
  change (inner ℝ (1 : ℂ) 1+inner ℝ (1 : ℂ) 1)+
    (inner ℝ Complex.I Complex.I+inner ℝ Complex.I Complex.I)=4
  norm_num [real_inner_self_eq_norm_sq]

/-- Generic maximum attainment, copied from the existing elementary helper;
it uses only continuity and a genuine Gaussian envelope. -/
theorem thermal_gaussian_envelope_attains_max {ρ : ℂ → ℝ} (hc : Continuous ρ)
    (hp : 0 < ρ 0) {a B : ℝ} (ha : 0 < a)
    (hb : ∀ x, ρ x ≤ B*Real.exp (-a*‖x‖^2)) :
    ∃ x : ℂ, ∀ y : ℂ, ρ y ≤ ρ x := by
  have hn : Tendsto (fun x : ℂ => ‖x‖^2) (cocompact ℂ) atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_norm_cocompact_atTop
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.const_mul_atTop ha)
  have ht : Tendsto (fun x : ℂ => B*Real.exp (-a*‖x‖^2)) (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using tendsto_const_nhds.mul he
  apply hc.exists_forall_ge' 0
  filter_upwards [ht.eventually (Iio_mem_nhds hp)] with x hx
  exact (hb x).trans hx.le

/-- The literal logarithmic density satisfies the physical pointwise
Laplacian identity. Its Poisson input is proved from the NEW compact-test
identity, rather than assumed as a PDE certificate. -/
theorem thermal_logDensity_laplacian_of_smooth_EL
    {ρ : ℂ → ℝ} {β C M : ℝ}
    (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2*ρ x))
    (hU2 : ContDiff ℝ 2 (equilibriumDensityPotential ρ))
    (hEL : ∀ x, Real.log (ρ x)=-β*(‖x‖^2/2+equilibriumDensityPotential ρ x)+C)
    (x : ℂ) : Laplacian.laplacian (fun y => Real.log (ρ y)) x =
      2*β*(Real.pi*ρ x-1) := by
  have hP := boundedDensityPotential_classical_poisson hρc hρ0 hρM hρi hρmass hρ2 hU2
  have hQ : ContDiff ℝ 2 ((1/2 : ℝ) • (fun x : ℂ => ‖x‖^2)) :=
    contDiff_const.smul (contDiff_norm_sq (𝕜 := ℝ))
  have hW : ContDiff ℝ 2 (((1/2 : ℝ) • (fun x : ℂ => ‖x‖^2)) + equilibriumDensityPotential ρ) :=
    hQ.add hU2
  have hA : ContDiff ℝ 2 ((-β) •
      (((1/2 : ℝ) • (fun x : ℂ => ‖x‖^2)) + equilibriumDensityPotential ρ)) :=
    hW.const_smul (-β)
  have hELfun : (fun x => Real.log (ρ x)) =
      (-β) • (((1/2 : ℝ) • (fun x : ℂ => ‖x‖^2)) + equilibriumDensityPotential ρ) +
        (fun _ => C) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEL x]
    ring
  have hLap (x : ℂ) : Laplacian.laplacian (fun y => Real.log (ρ y)) x =
      2*β*(Real.pi*ρ x-1) := by
    rw [hELfun,
      hA.contDiffAt.laplacian_add contDiff_const.contDiffAt,
      laplacian_const, Pi.zero_apply, add_zero, laplacian_smul (-β) hW.contDiffAt,
      hQ.contDiffAt.laplacian_add hU2.contDiffAt,
      laplacian_smul (1/2 : ℝ) (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt,
      thermal_complex_laplacian_norm_sq, hP x]
    simp only [smul_eq_mul]
    ring
  exact hLap x

/-- The sharp cap from the actual classical Poisson and EL equations at an
actually attained global maximum. The maximum-sign step is NEW. -/
theorem thermal_sharp_cap_of_smooth_bounded_EL
    {ρ : ℂ → ℝ} {β C M : ℝ} (hβ : 0 < β)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x, ρ x)=1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖^2*ρ x))
    (hUs : ContDiff ℝ (⊤ : ℕ∞) (equilibriumDensityPotential ρ))
    (hEL : ∀ x, Real.log (ρ x)=-β*(‖x‖^2/2+equilibriumDensityPotential ρ x)+C) :
    ∀ x, ρ x ≤ Real.pi⁻¹ := by
  have hρm := hρs.continuous.measurable
  have hρ0 := fun x => (hρpos x).le
  have hU2 : ContDiff ℝ 2 (equilibriumDensityPotential ρ) := hUs.of_le (by simp)
  have hρC2 : ContDiff ℝ 2 ρ := hρs.of_le (by simp)
  have hlog : ContDiff ℝ 2 (fun x => Real.log (ρ x)) := hρC2.log (fun x => (hρpos x).ne')
  have hLap := thermal_logDensity_laplacian_of_smooth_EL hρs.continuous
    hρ0 hρM hρi hρmass hρ2 hU2 hEL
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  let B := Real.exp (C+β*((∫ y : ℂ, equilibriumLogMoment y*ρ y)+1))
  have hbound (x : ℂ) : ρ x ≤ B*Real.exp (-(β/4)*‖x‖^2) := by
    have h := equilibrium_EL_gaussian_bound hβ (hρpos x) x (hEL x)
      (equilibriumDensityPotential_lower hρm hρ0 hρM hρi hρmass hρL x)
    have he : -β*‖x‖^2/4 = -(β/4)*‖x‖^2 := by ring
    simpa only [B, he] using h
  obtain ⟨c, hmax⟩ := thermal_gaussian_envelope_attains_max hρs.continuous
    (hρpos 0) (by positivity : (0 : ℝ) < β/4) hbound
  have hlogmax (y : ℂ) : Real.log (ρ y) ≤ Real.log (ρ c) :=
    Real.log_le_log (hρpos y) (hmax y)
  have hsign := laplacian_nonpos_at_globalMax hlog c hlogmax
  rw [hLap c] at hsign
  have hsmall : Real.pi*ρ c ≤ 1 := by
    by_contra hn
    have hp := mul_pos (by positivity : 0 < 2*β) (sub_pos.mpr (lt_of_not_ge hn))
    exact (not_lt_of_ge hsign) hp
  have hc : ρ c ≤ Real.pi⁻¹ := by
    have h := (le_div_iff₀ Real.pi_pos).mpr
      (show ρ c*Real.pi ≤ 1 by simpa only [mul_comm] using hsmall)
    simpa only [one_div] using h
  exact fun x => (hmax x).trans hc

end RepulsiveCoulomb.PaperRoute
