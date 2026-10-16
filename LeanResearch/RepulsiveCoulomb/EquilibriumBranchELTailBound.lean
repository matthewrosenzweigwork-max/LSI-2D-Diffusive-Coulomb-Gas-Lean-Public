module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchThermalEulerLagrange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Tail bounds before any regularity or radiality argument. The lower
potential estimate only uses actual row integrability; finite absolute pair
energy and positivity give that input almost everywhere. The canonical
Gaussian-polynomial exponent beta is preserved exactly. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

/-- Lower potential bound at any point where the actual row is integrable,
without assuming an L-infinity bound on the density. -/
theorem equilibriumDensityPotential_lower_of_integrable {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ y : ℂ, ρ y) = 1)
    (hρL : Integrable (fun y : ℂ => equilibriumLogMoment y * ρ y)) (x : ℂ)
    (hx : Integrable (fun y : ℂ => equilibriumLogKernel (x - y) * ρ y)) :
    -equilibriumLogMoment x - (∫ y : ℂ, equilibriumLogMoment y * ρ y) ≤
      equilibriumDensityPotential ρ x := by
  have hi := (hρi.const_mul (-equilibriumLogMoment x)).sub hρL
  have hm := integral_mono hi hx (fun y => by
    have h := mul_le_mul_of_nonneg_right (equilibriumLogKernel_sub_lower x y) (hρ0 y)
    dsimp only [Pi.sub_apply]
    nlinarith)
  change (∫ y : ℂ, -equilibriumLogMoment x * ρ y - equilibriumLogMoment y * ρ y) ≤
    equilibriumDensityPotential ρ x at hm
  rw [integral_sub (hρi.const_mul _) hρL, integral_const_mul, hρmass, mul_one] at hm
  exact hm

/-- Positivity and finite pair energy really supply volume-a.e. row
integrability even when the base density is not yet bounded. -/
theorem equilibriumLogKernel_mul_integrable_ae {ρ : ℂ → ℝ}
    (hρpos : ∀ᵐ x : ℂ, 0 < ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    ∀ᵐ x : ℂ, Integrable (fun y : ℂ => equilibriumLogKernel (x - y) * ρ y) := by
  filter_upwards [hρpos, hG.prod_right_ae] with x hx hi
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hx.ne') _).mp hi

/-- The exact zeroth-order Gaussian-polynomial tail from the manuscript EL
normalization and the logarithmic lower potential bound. -/
theorem equilibrium_EL_polynomial_gaussian_bound {β r C ℓ U : ℝ} (hβ : 0 < β)
    (hr : 0 < r) (x : ℂ)
    (hEL : Real.log r = -β * (‖x‖ ^ 2 / 2 + U) + C)
    (hU : -equilibriumLogMoment x - ℓ ≤ U) :
    r ≤ Real.exp (C + β * ℓ) * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2) := by
  have hlog : Real.log r ≤ (C + β * ℓ) + β * equilibriumLogMoment x - β * ‖x‖ ^ 2 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hU hβ.le
    rw [hEL]
    nlinarith
  calc
    r = Real.exp (Real.log r) := (Real.exp_log hr).symm
    _ ≤ Real.exp ((C + β * ℓ) + β * equilibriumLogMoment x - β * ‖x‖ ^ 2 / 2) := Real.exp_le_exp.mpr hlog
    _ = _ := by
      rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖x‖), ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold equilibriumLogMoment
      ring

/-- A coarser Gaussian bound gives a finite global cap before the sharp
Laplacian maximum argument is available. -/
theorem equilibrium_EL_gaussian_bound {β r C ℓ U : ℝ} (hβ : 0 < β)
    (hr : 0 < r) (x : ℂ)
    (hEL : Real.log r = -β * (‖x‖ ^ 2 / 2 + U) + C)
    (hU : -equilibriumLogMoment x - ℓ ≤ U) :
    r ≤ Real.exp (C + β * (ℓ + 1)) * Real.exp (-β * ‖x‖ ^ 2 / 4) := by
  have hL := equilibriumLogMoment_le_quadratic (by norm_num : (0 : ℝ) < 1 / 4) x
  norm_num at hL
  have hlog : Real.log r ≤ C + β * (ℓ + 1) - β * ‖x‖ ^ 2 / 4 := by
    have hm := mul_le_mul_of_nonneg_left hU hβ.le
    have hmL := mul_le_mul_of_nonneg_left hL hβ.le
    rw [hEL]
    nlinarith
  calc
    r = Real.exp (Real.log r) := (Real.exp_log hr).symm
    _ ≤ Real.exp (C + β * (ℓ + 1) - β * ‖x‖ ^ 2 / 4) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The finite preliminary cap follows from a.e. EL and actual finite energy,
so it is a consequence rather than an assumption of the bounded-density stage. -/
theorem equilibriumDensity_EL_bounded_ae {β C : ℝ} (hβ : 0 < β) {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hρpos : ∀ᵐ x : ℂ, 0 < ρ x)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume))
    (hEL : ∀ᵐ x : ℂ, Real.log (ρ x) = -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential ρ x) + C) :
    ∀ᵐ x : ℂ, ρ x ≤ Real.exp (C + β * ((∫ y : ℂ, equilibriumLogMoment y * ρ y) + 1)) := by
  have hρL := equilibriumLogMoment_mul_integrable hρm hρ0 hρi hρ2
  filter_upwards [hρpos, hEL, equilibriumLogKernel_mul_integrable_ae hρpos hG] with x hxpos hxEL hxi
  have hU := equilibriumDensityPotential_lower_of_integrable hρ0 hρi hρmass hρL x hxi
  have hb := equilibrium_EL_gaussian_bound hβ hxpos x hxEL hU
  have he : Real.exp (-β * ‖x‖ ^ 2 / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
  exact hb.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

/-- Null-set corrections of a density leave its literal potential unchanged
at every point, not merely almost everywhere. -/
theorem equilibriumDensityPotential_congr_ae {ρ σ : ℂ → ℝ} (h : ρ =ᵐ[volume] σ) (x : ℂ) :
    equilibriumDensityPotential ρ x = equilibriumDensityPotential σ x := by
  unfold equilibriumDensityPotential
  apply integral_congr_ae
  exact h.mono (fun y hy => by simp only [hy])

end RepulsiveCoulomb
