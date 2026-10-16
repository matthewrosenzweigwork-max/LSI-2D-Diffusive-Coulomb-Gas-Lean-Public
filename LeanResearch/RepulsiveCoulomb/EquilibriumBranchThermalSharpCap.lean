import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalSmooth
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCirclePotentialDifference
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-! The sharp cap 1/pi from an actual attained density maximum and the exact
circular mean identity. Continuity plus the proved Gaussian envelope gives a
global maximum. The exact error mass pi*epsilon^2/2 yields the contradiction
when the density is above 1/pi on a small disk. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- Positive continuous densities with an actual Gaussian envelope attain a
maximum; no compactness of the plane is assumed. -/
theorem equilibrium_gaussian_envelope_attains_max {ρ : ℂ → ℝ} (hc : Continuous ρ)
    (hp : 0 < ρ 0) {a B : ℝ} (ha : 0 < a)
    (hb : ∀ x, ρ x ≤ B * Real.exp (-a * ‖x‖ ^ 2)) :
    ∃ x : ℂ, ∀ y : ℂ, ρ y ≤ ρ x := by
  have hn : Tendsto (fun x : ℂ => ‖x‖ ^ 2) (cocompact ℂ) atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_norm_cocompact_atTop
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.const_mul_atTop ha)
  have ht : Tendsto (fun x : ℂ => B * Real.exp (-a * ‖x‖ ^ 2)) (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using tendsto_const_nhds.mul he
  apply hc.exists_forall_ge' 0
  filter_upwards [ht.eventually (Iio_mem_nhds hp)] with x hx
  exact (hb x).trans hx.le

/-- Exact circular mean increment of log rho under the manuscript EL equation. -/
theorem equilibrium_EL_circle_log_increment {β C M r : ℝ} (hr : 0 < r)
    {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUc : Continuous (equilibriumDensityPotential ρ))
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C)
    (c : ℂ) :
    (∫ z : ℂ, Real.log (ρ z) ∂equilibriumCircleMeasure c r) - Real.log (ρ c) =
      β * ((∫ y : ℂ, equilibriumCircularError r (y - c) * ρ y) - r ^ 2 / 2) := by
  have hnorm : Integrable (fun z : ℂ => ‖z‖ ^ 2) (equilibriumCircleMeasure c r) :=
    integrable_equilibriumCircleMeasure_of_circleIntegrable c r (continuous_norm.pow 2).measurable
      (continuous_norm.pow 2).continuousOn.circleIntegrable'
  have hU : Integrable (equilibriumDensityPotential ρ) (equilibriumCircleMeasure c r) :=
    integrable_equilibriumCircleMeasure_of_circleIntegrable c r hUc.measurable hUc.continuousOn.circleIntegrable'
  have h₁ := integral_add (hnorm.div_const 2) hU
  have h₂ := integral_add (((hnorm.div_const 2).add hU).const_mul (-β))
    (integrable_const (μ := equilibriumCircleMeasure c r) C)
  dsimp only [Pi.add_apply] at h₁ h₂
  have he : (fun z : ℂ => Real.log (ρ z)) =
      (fun z : ℂ => -β * (‖z‖ ^ 2 / 2 + equilibriumDensityPotential ρ z) + C) := funext hEL
  rw [he, h₂, integral_const_mul, h₁, integral_div,
    integral_equilibriumCircleMeasure_norm_sq c hr.le,
    equilibriumDensityPotential_circle_average hr hρm hρ0 hρM hρi hρmass hρ2 c,
    hEL c]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Every positive bounded continuous pointwise-EL density has the sharp cap.
The maximum and all circular integrals are actual constructions. -/
theorem equilibrium_pointwise_EL_sharp_cap {β C M : ℝ} (hβ : 0 < β)
    {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (hρM : ∀ x, ρ x ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hUc : Continuous (equilibriumDensityPotential ρ))
    (hEL : ∀ x, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) :
    ∀ x, ρ x ≤ Real.pi⁻¹ := by
  have hρm := hρc.measurable
  have hρ0 := fun x => (hρpos x).le
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  let B := Real.exp (C + β * ((∫ y : ℂ, equilibriumLogMoment y * ρ y) + 1))
  have hbound (x : ℂ) : ρ x ≤ B * Real.exp (-(β / 4) * ‖x‖ ^ 2) := by
    have h := equilibrium_EL_gaussian_bound hβ (hρpos x) x (hEL x)
      (equilibriumDensityPotential_lower hρm hρ0 hρM hρi hρmass hρL x)
    have he : -β * ‖x‖ ^ 2 / 4 = -(β / 4) * ‖x‖ ^ 2 := by ring
    simpa only [he] using h
  obtain ⟨c, hmax⟩ := equilibrium_gaussian_envelope_attains_max hρc (hρpos 0)
    (by positivity : 0 < β / 4) hbound
  have hc : ρ c ≤ Real.pi⁻¹ := by
    by_contra hnot
    have hc' : Real.pi⁻¹ < ρ c := lt_of_not_ge hnot
    let m : ℝ := (Real.pi⁻¹ + ρ c) / 2
    have hm₁ : Real.pi⁻¹ < m := by dsimp only [m]; linarith
    have hm₂ : m < ρ c := by dsimp only [m]; linarith
    have hevent : ∀ᶠ y in 𝓝 c, m < ρ y := hρc.continuousAt.eventually (Ioi_mem_nhds hm₂)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
    have hlocal : ∀ y ∈ ball c r, m ≤ ρ y := fun y hy => (hball hy).le
    have hE := equilibriumCircularError_local_lower hr hρm hρ0 hρM c hlocal
    have hmpi : 1 < m * Real.pi := by
      have h := (div_lt_iff₀ Real.pi_pos).mp (show 1 / Real.pi < m by simpa only [one_div] using hm₁)
      nlinarith
    have hgap : r ^ 2 / 2 < ∫ y : ℂ, equilibriumCircularError r (y - c) * ρ y := by
      have hh := mul_lt_mul_of_pos_right hmpi (div_pos (sq_pos_of_pos hr) (by norm_num : (0 : ℝ) < 2))
      nlinarith
    have hinc := equilibrium_EL_circle_log_increment hr hρm hρ0 hρM hρi hρmass hρ2 hUc hEL c
    have hlc : Continuous (fun z : ℂ => Real.log (ρ z)) := hρc.log (fun z => (hρpos z).ne')
    have hli : Integrable (fun z : ℂ => Real.log (ρ z)) (equilibriumCircleMeasure c r) :=
      integrable_equilibriumCircleMeasure_of_circleIntegrable c r hlc.measurable hlc.continuousOn.circleIntegrable'
    have hupper := integral_mono hli (integrable_const (μ := equilibriumCircleMeasure c r) (Real.log (ρ c)))
      (fun z => Real.log_le_log (hρpos z) (hmax z))
    simp only [integral_const, probReal_univ, one_smul] at hupper
    have hpositive := mul_pos hβ (sub_pos.mpr hgap)
    linarith
  exact fun x => (hmax x).trans hc

end RepulsiveCoulomb
