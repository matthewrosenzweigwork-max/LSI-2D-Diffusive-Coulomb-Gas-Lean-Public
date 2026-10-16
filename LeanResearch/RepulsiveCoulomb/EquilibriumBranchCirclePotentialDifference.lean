import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNewtonCircleIdentity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleMoments
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchErrorMoments

/-! Exact circular mean increment of an actual bounded-density potential and
the sharp local error lower bound. Both retain pi*epsilon^2/2 and use genuine
circle/background Fubini, including the singular circle measure class. -/
noncomputable section
open MeasureTheory Real Set Filter Metric
namespace RepulsiveCoulomb

theorem equilibriumCircularError_sub_symm (r : ℝ) (x y : ℂ) :
    equilibriumCircularError r (x - y) = equilibriumCircularError r (y - x) := by
  simp only [equilibriumCircularError, equilibriumLogPositive, equilibriumLogKernel,
    norm_smul, norm_sub_rev]

theorem equilibriumCircularError_eq_zero_of_le_norm {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : r ≤ ‖z‖) : equilibriumCircularError r z = 0 := by
  have hn : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hz)
  rw [equilibriumCircularError_eq_sub hr hn]
  simp only [equilibriumLogKernel, equilibriumCircularKernel, max_eq_right hz, sub_self]

/-- Averaging the literal potential on a circle subtracts exactly the local
circular error. There is no density interpretation of the circle measure. -/
theorem equilibriumDensityPotential_circle_average {ρ : ℂ → ℝ} {M r : ℝ}
    (hr : 0 < r) (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2 * ρ y)) (c : ℂ) :
    (∫ z : ℂ, equilibriumDensityPotential ρ z ∂equilibriumCircleMeasure c r) =
      equilibriumDensityPotential ρ c - ∫ y : ℂ, equilibriumCircularError r (y - c) * ρ y := by
  let μ := equilibriumDensityMeasure ρ
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  have hμ2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ :=
    (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr hρ2
  have hμ1 : Integrable (fun y : ℂ => ‖y‖) μ := by
    apply (hμ2.add (integrable_const (μ := μ) (1 : ℝ))).mono' continuous_norm.measurable.aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
      nlinarith [sq_nonneg (‖y‖ - 1)])
  have hcross := equilibriumMeasure_circle_logEnergy_integrable hμ1 c hr
  have hswap : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((equilibriumCircleMeasure c r).prod μ) := by
    apply hcross.swap.congr
    exact Eventually.of_forall (fun p => by
      change equilibriumLogKernel (p.2 - p.1) = equilibriumLogKernel (p.1 - p.2)
      simp only [equilibriumLogKernel, norm_sub_rev])
  have hmean : (∫ z : ℂ, equilibriumDensityPotential ρ z ∂equilibriumCircleMeasure c r) =
      ∫ y : ℂ, equilibriumCircularKernel r (c - y) * ρ y := by
    calc
      _ = ∫ z : ℂ, ∫ y : ℂ, equilibriumLogKernel (z - y) ∂μ ∂equilibriumCircleMeasure c r := by
        apply integral_congr_ae
        exact Eventually.of_forall (equilibriumDensityPotential_eq_measureIntegral hρm hρ0)
      _ = ∫ y : ℂ, ∫ z : ℂ, equilibriumLogKernel (z - y) ∂equilibriumCircleMeasure c r ∂μ :=
        integral_integral_swap hswap
      _ = ∫ y : ℂ, equilibriumCircularKernel r (c - y) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => equilibriumCircleMeasure_log_potential c y hr)
      _ = _ := by
        rw [integral_equilibriumDensityMeasure hρm hρ0]
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by ring)
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  have hk := equilibriumLogKernel_mul_integrable hρm hρ0 hρM hρi hρL c
  have hE : Integrable (fun y : ℂ => equilibriumCircularError r (y - c) * ρ y) := by
    simpa only [pow_one] using equilibriumCircularError_pow_mul_integrable hr 1 (by norm_num) hρm hρ0 hρM c
  have he : (fun y : ℂ => equilibriumLogKernel (c - y) * ρ y - equilibriumCircularError r (y - c) * ρ y) =ᵐ[volume]
      (fun y : ℂ => equilibriumCircularKernel r (c - y) * ρ y) := by
    filter_upwards [volume.ae_ne c] with y hy
    rw [← equilibriumCircularError_sub_symm r c y,
      equilibriumCircularError_eq_sub hr (sub_ne_zero.mpr hy.symm)]
    ring
  rw [hmean, ← integral_congr_ae he, integral_sub hk hE]
  rfl

/-- A local density lower bound gives the exact sharp local circular error. -/
theorem equilibriumCircularError_local_lower {ρ : ℂ → ℝ} {M r m : ℝ}
    (hr : 0 < r) (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρM : ∀ y, ρ y ≤ M)
    (c : ℂ) (hlocal : ∀ y ∈ ball c r, m ≤ ρ y) :
    m * Real.pi * r ^ 2 / 2 ≤ ∫ y : ℂ, equilibriumCircularError r (y - c) * ρ y := by
  have hE : Integrable (fun y : ℂ => equilibriumCircularError r (y - c) * ρ y) := by
    simpa only [pow_one] using equilibriumCircularError_pow_mul_integrable hr 1 (by norm_num) hρm hρ0 hρM c
  have hc := ((equilibriumCircularError_integrable hr).comp_sub_right c).const_mul m
  have h := integral_mono hc hE (fun y => by
    by_cases hy : y ∈ ball c r
    · have hm := mul_le_mul_of_nonneg_left (hlocal y hy) (equilibriumCircularError_nonneg r (y - c))
      simpa only [mul_comm] using hm
    · have hnorm : r ≤ ‖y - c‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hy
      rw [equilibriumCircularError_eq_zero_of_le_norm hr hnorm]
      simp only [mul_zero, zero_mul, le_refl])
  rw [integral_const_mul, integral_sub_right_eq_self, integral_equilibriumCircularError hr] at h
  nlinarith

end RepulsiveCoulomb
