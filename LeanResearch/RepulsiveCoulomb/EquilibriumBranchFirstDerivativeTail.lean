module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceCompactBounds

@[expose] public section

/-! The first physical derivative tail, with exact beta+1 polynomial exponent.
The sharp density cap gives 0<=1-2*pi*J<=1, so the actual Cartesian score
controls the full real Fréchet derivative without changing gradient scaling. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem equilibriumReference_radialAverage_bounds {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) :
    0 ≤ equilibriumRadialAverage R.density x ∧
      equilibriumRadialAverage R.density x ≤ Real.pi⁻¹ / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => s * R.density (s • x)) volume 0 1 :=
    (continuous_id.mul (R.smooth.continuous.comp (by fun_prop))).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun s : ℝ => s * Real.pi⁻¹) volume 0 1 :=
    (continuous_id.mul continuous_const).intervalIntegrable _ _
  refine ⟨?_, ?_⟩
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro s hs
    exact mul_nonneg hs.1 (R.positive _).le
  · have h := intervalIntegral.integral_mono_on zero_le_one hi hj (fun s hs =>
      mul_le_mul_of_nonneg_left (R.cap (s • x)) hs.1)
    rw [intervalIntegral.integral_mul_const] at h
    norm_num at h
    simpa [equilibriumRadialAverage, div_eq_mul_inv, mul_comm] using h

theorem equilibriumReference_scoreFactor_bounds {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) :
    0 ≤ 1 - 2 * Real.pi * equilibriumRadialAverage R.density x ∧
      1 - 2 * Real.pi * equilibriumRadialAverage R.density x ≤ 1 := by
  obtain ⟨h0, h1⟩ := equilibriumReference_radialAverage_bounds R x
  have hp := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * Real.pi)
  have he : 2 * Real.pi * (Real.pi⁻¹ / 2) = 1 := by field_simp
  rw [he] at hp
  constructor
  · linarith
  · nlinarith [Real.pi_pos]

/-- The actual full physical first derivative obeys the radial score bound. -/
theorem equilibriumReference_fderiv_norm_le {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    ‖fderiv ℝ R.density x‖ ≤ β * R.density x * ‖x‖ := by
  have hD := equilibrium_pointwise_EL_hasFDerivAt_score hβ R.smooth.continuous.measurable
    R.positive R.cap R.integrable R.mass_one R.secondMoment_integrable R.radial R.eulerLagrange x
  obtain ⟨h0, h1⟩ := equilibriumReference_scoreFactor_bounds R x
  rw [hD.fderiv, equilibriumScoreDerivative, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) h0) (R.positive x).le)]
  have h := mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hβ.le (R.positive x).le) (norm_nonneg x))
  nlinarith

/-- Exact first-order Gaussian-polynomial tail, beta+1, on all of the plane. -/
theorem equilibriumReference_firstDerivative_tail {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    ‖fderiv ℝ R.density x‖ ≤ (β * R.tailConstant) *
      (1 + ‖x‖) ^ (β + 1) * Real.exp (-β * ‖x‖ ^ 2 / 2) := by
  have hK := R.tailConstant_pos
  have hρ := mul_le_mul_of_nonneg_left (R.tail x) hβ.le
  have h := mul_le_mul_of_nonneg_right hρ (norm_nonneg x)
  have htail0 : 0 ≤ β * (R.tailConstant * (1 + ‖x‖) ^ β * Real.exp (-β * ‖x‖ ^ 2 / 2)) := by positivity
  have hx : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  have h' := mul_le_mul_of_nonneg_left hx htail0
  apply (equilibriumReference_fderiv_norm_le hβ R x).trans (h.trans ?_)
  apply h'.trans_eq
  rw [Real.rpow_add (by positivity : 0 < 1 + ‖x‖), Real.rpow_one]
  ring

/-- The first derivative is globally bounded by an explicit finite constant,
which is the domination input for the first radial-average derivative. -/
theorem equilibriumReference_fderiv_globally_bounded {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖fderiv ℝ R.density x‖ ≤ D := by
  have hK := R.tailConstant_pos
  let D := (β * R.tailConstant) * Real.exp ((β + 1) ^ 2 / (2 * (β / 2)))
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro x
  have h := equilibriumReference_firstDerivative_tail hβ R x
  have he : -β * ‖x‖ ^ 2 / 2 = -(β / 2) * ‖x‖ ^ 2 := by ring
  rw [he] at h
  have hp := mul_le_mul_of_nonneg_left
    (equilibriumPolynomialGaussian_bound (by linarith : 0 ≤ β + 1) (half_pos hβ) x)
    (mul_nonneg hβ.le R.tailConstant_pos.le)
  have hx : Real.exp (-(β / 2 / 2) * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
  have hh := mul_le_mul_of_nonneg_left hx (show 0 ≤ D by dsimp only [D]; positivity)
  dsimp only [equilibriumPolynomialGaussian] at hp
  dsimp only [D] at hh ⊢
  nlinarith

end RepulsiveCoulomb
