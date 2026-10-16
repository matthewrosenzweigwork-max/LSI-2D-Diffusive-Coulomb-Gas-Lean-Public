module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceBounds

@[expose] public section

/-! One explicit Gaussian-polynomial envelope for every actual equilibrium
reference in a compact positive-temperature interval. The constants depend
only on the interval endpoints, not particle number or a temperature modulus
of continuity. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumCompactEnvelopeConstant (βlo βhi : ℝ) : ℝ :=
  (βhi / (2 * Real.pi)) * Real.exp (βhi * (equilibriumCompactLogBound βlo + 1 / 2))

theorem equilibriumCompactEnvelopeConstant_pos {βlo βhi : ℝ} (hlo : 0 < βlo) (hord : βlo ≤ βhi) :
    0 < equilibriumCompactEnvelopeConstant βlo βhi := by
  unfold equilibriumCompactEnvelopeConstant
  exact mul_pos (div_pos (hlo.trans_le hord) (by positivity)) (Real.exp_pos _)

/-- The potentially temperature-dependent EL normalization has an explicit
bound after combining the exact Gaussian normalization and logarithmic moment. -/
theorem equilibriumReference_tail_prefactor_bound {β βlo βhi : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi)
    (R : EquilibriumConstructedReference β) :
    Real.exp (R.elConstant + β * (∫ y : ℂ, equilibriumLogMoment y * R.density y)) ≤
      equilibriumCompactEnvelopeConstant βlo βhi := by
  have hβ : 0 < β := hlo.trans_le hβlo
  have hhi : 0 < βhi := hβ.trans_le hβhi
  let L : ℝ := ∫ y : ℂ, equilibriumLogMoment y * R.density y
  have hL : L ≤ equilibriumCompactLogBound βlo := equilibriumReference_logMoment_bound hlo hβlo R
  have hL0 : 0 ≤ L := integral_nonneg (fun y => mul_nonneg (equilibriumLogMoment_nonneg y) (R.positive y).le)
  have hC := equilibriumReference_exp_elConstant_le hβ R
  have harg : β * (L + 1 / 2) ≤ βhi * (equilibriumCompactLogBound βlo + 1 / 2) :=
    mul_le_mul hβhi (add_le_add hL le_rfl) (by linarith) hhi.le
  have hcoef : β / (2 * Real.pi) ≤ βhi / (2 * Real.pi) :=
    div_le_div_of_nonneg_right hβhi (by positivity)
  calc
    Real.exp (R.elConstant + β * L) = Real.exp R.elConstant * Real.exp (β * L) := Real.exp_add _ _
    _ ≤ ((β / (2 * Real.pi)) * Real.exp (β / 2)) * Real.exp (β * L) :=
      mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ = (β / (2 * Real.pi)) * Real.exp (β * (L + 1 / 2)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (βhi / (2 * Real.pi)) * Real.exp (βhi * (equilibriumCompactLogBound βlo + 1 / 2)) :=
      mul_le_mul hcoef (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
    _ = equilibriumCompactEnvelopeConstant βlo βhi := rfl

/-- The common density envelope over the full compact beta interval. -/
theorem equilibriumReference_uniform_envelope {β βlo βhi : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi)
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    R.density x ≤ equilibriumCompactEnvelopeConstant βlo βhi *
      equilibriumPolynomialGaussian βhi (βlo / 2) x := by
  have hβ : 0 < β := hlo.trans_le hβlo
  have htail := equilibrium_EL_polynomial_gaussian_bound hβ (R.positive x) x (R.eulerLagrange x)
    (equilibriumReference_potential_lower R x)
  have hA := equilibriumReference_tail_prefactor_bound hlo hβlo hβhi R
  have hB0 := (equilibriumCompactEnvelopeConstant_pos hlo (hβlo.trans hβhi)).le
  have hp : (1 + ‖x‖) ^ β ≤ (1 + ‖x‖) ^ βhi :=
    Real.rpow_le_rpow_of_exponent_le (by have := norm_nonneg x; linarith) hβhi
  have he : Real.exp (-β * ‖x‖ ^ 2 / 2) ≤ Real.exp (-(βlo / 2) * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hβlo (sq_nonneg ‖x‖)
    nlinarith
  have hh := mul_le_mul hA hp (Real.rpow_nonneg (by positivity) _) hB0
  have h := mul_le_mul hh he (Real.exp_pos _).le
    (mul_nonneg hB0 (Real.rpow_nonneg (by positivity) _))
  apply htail.trans
  simpa only [equilibriumPolynomialGaussian, mul_assoc] using h

end RepulsiveCoulomb
