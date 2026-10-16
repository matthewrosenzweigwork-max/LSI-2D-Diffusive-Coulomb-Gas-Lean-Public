import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceEnvelope

/-! Actual compact-temperature moment bounds for the constructed reference.
All real polynomial exponents m>=0 and every theta>0 are preserved. Bounds
use one explicit endpoint-dependent Gaussian envelope and contain no particle
number or assumed moment/exponential-integrability estimate. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumCompactMomentBound (βlo βhi m : ℝ) : ℝ :=
  equilibriumCompactEnvelopeConstant βlo βhi * Real.exp ((m + βhi) ^ 2 / βlo) * (4 * Real.pi / βlo)

def equilibriumCompactPotentialBound (βlo βhi θ : ℝ) : ℝ :=
  (equilibriumCompactEnvelopeConstant βlo βhi * Real.exp (θ * βhi * equilibriumCompactLogBound βlo)) *
    Real.exp (((1 + θ) * βhi) ^ 2 / βlo) * (4 * Real.pi / βlo)

/-- Every real polynomial moment is actually integrable, with one uniform
bound on the compact beta interval. -/
theorem equilibriumReference_polynomial_moment_bound {β βlo βhi m : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) (hm : 0 ≤ m)
    (R : EquilibriumConstructedReference β) :
    Integrable (fun x : ℂ => (1 + ‖x‖) ^ m) R.measure ∧
      (∫ x : ℂ, (1 + ‖x‖) ^ m ∂R.measure) ≤ equilibriumCompactMomentBound βlo βhi m := by
  have hhi : 0 < βhi := hlo.trans_le (hβlo.trans hβhi)
  have hB := (equilibriumCompactEnvelopeConstant_pos hlo (hβlo.trans hβhi)).le
  have hρm := R.smooth.continuous.measurable
  have hρ0 := fun x => (R.positive x).le
  have hw : Measurable (fun x : ℂ => (1 + ‖x‖) ^ m * R.density x) :=
    (((Real.continuous_rpow_const hm).comp (continuous_const.add continuous_norm)).measurable).mul hρm
  have hbound (x : ℂ) : (1 + ‖x‖) ^ m * R.density x ≤
      equilibriumCompactEnvelopeConstant βlo βhi * equilibriumPolynomialGaussian (m + βhi) (βlo / 2) x := by
    have h := mul_le_mul_of_nonneg_left (equilibriumReference_uniform_envelope hlo hβlo hβhi R x)
      (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) m)
    apply h.trans_eq
    unfold equilibriumPolynomialGaussian
    rw [Real.rpow_add (by positivity : 0 < 1 + ‖x‖)]
    ring
  obtain ⟨hi, hb⟩ := equilibrium_integrable_and_integral_le_of_polynomial_gaussian hw
    (fun x => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hρ0 x))
    (add_nonneg hm hhi.le) (half_pos hlo) hB hbound
  have hden : 2 * (βlo / 2) = βlo := by ring
  have hmass : 2 * Real.pi / (βlo / 2) = 4 * Real.pi / βlo := by field_simp <;> ring
  rw [hden, hmass] at hb
  refine ⟨?_, ?_⟩
  · rw [← R.density_measure]
    exact (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr hi
  · rw [← R.density_measure, integral_equilibriumDensityMeasure hρm hρ0]
    have he : (∫ x : ℂ, R.density x * (1 + ‖x‖) ^ m) = ∫ x : ℂ, (1 + ‖x‖) ^ m * R.density x :=
      integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    rw [he]
    exact hb

/-- Pointwise domination for the exponential of the actual potential times its
density. The exponent theta is unrestricted above zero. -/
theorem equilibriumReference_potential_weight_envelope {β βlo βhi θ : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) (hθ : 0 < θ)
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    Real.exp (-θ * β * equilibriumDensityPotential R.density x) * R.density x ≤
      (equilibriumCompactEnvelopeConstant βlo βhi * Real.exp (θ * βhi * equilibriumCompactLogBound βlo)) *
        equilibriumPolynomialGaussian ((1 + θ) * βhi) (βlo / 2) x := by
  have hβ : 0 < β := hlo.trans_le hβlo
  have hhi : 0 < βhi := hβ.trans_le hβhi
  have hB := (equilibriumCompactEnvelopeConstant_pos hlo (hβlo.trans hβhi)).le
  let L : ℝ := ∫ y : ℂ, equilibriumLogMoment y * R.density y
  have hL0 : 0 ≤ L := integral_nonneg (fun y => mul_nonneg (equilibriumLogMoment_nonneg y) (R.positive y).le)
  have hL : L ≤ equilibriumCompactLogBound βlo := equilibriumReference_logMoment_bound hlo hβlo R
  have hprod : β * (equilibriumLogMoment x + L) ≤
      βhi * (equilibriumLogMoment x + equilibriumCompactLogBound βlo) :=
    mul_le_mul hβhi (add_le_add le_rfl hL) (add_nonneg (equilibriumLogMoment_nonneg x) hL0) hhi.le
  have hθprod := mul_le_mul_of_nonneg_left hprod hθ.le
  have hU := mul_le_mul_of_nonneg_left (equilibriumReference_potential_lower R x)
    (mul_nonneg hθ.le hβ.le)
  have hlog : -θ * β * equilibriumDensityPotential R.density x + βhi * equilibriumLogMoment x ≤
      θ * βhi * equilibriumCompactLogBound βlo + ((1 + θ) * βhi) * equilibriumLogMoment x := by
    dsimp only [L] at hθprod
    nlinarith
  have hf : Real.exp (-θ * β * equilibriumDensityPotential R.density x) * (1 + ‖x‖) ^ βhi ≤
      Real.exp (θ * βhi * equilibriumCompactLogBound βlo) * (1 + ‖x‖) ^ ((1 + θ) * βhi) := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖x‖),
      Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖x‖), ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold equilibriumLogMoment at hlog
    nlinarith
  calc
    _ ≤ Real.exp (-θ * β * equilibriumDensityPotential R.density x) *
        (equilibriumCompactEnvelopeConstant βlo βhi * equilibriumPolynomialGaussian βhi (βlo / 2) x) :=
      mul_le_mul_of_nonneg_left (equilibriumReference_uniform_envelope hlo hβlo hβhi R x) (Real.exp_pos _).le
    _ = equilibriumCompactEnvelopeConstant βlo βhi *
        (Real.exp (-θ * β * equilibriumDensityPotential R.density x) * (1 + ‖x‖) ^ βhi) *
          Real.exp (-(βlo / 2) * ‖x‖ ^ 2) := by unfold equilibriumPolynomialGaussian; ring
    _ ≤ equilibriumCompactEnvelopeConstant βlo βhi *
        (Real.exp (θ * βhi * equilibriumCompactLogBound βlo) * (1 + ‖x‖) ^ ((1 + θ) * βhi)) *
          Real.exp (-(βlo / 2) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hB) (Real.exp_pos _).le
    _ = _ := by unfold equilibriumPolynomialGaussian; ring

/-- Actual exponential-potential integrability and its compact-beta bound. -/
theorem equilibriumReference_potential_exponential_bound {β βlo βhi θ : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) (hθ : 0 < θ)
    (R : EquilibriumConstructedReference β) :
    Integrable (fun x : ℂ => Real.exp (-θ * β * equilibriumDensityPotential R.density x)) R.measure ∧
      (∫ x : ℂ, Real.exp (-θ * β * equilibriumDensityPotential R.density x) ∂R.measure) ≤
        equilibriumCompactPotentialBound βlo βhi θ := by
  have hhi : 0 < βhi := hlo.trans_le (hβlo.trans hβhi)
  have hρm := R.smooth.continuous.measurable
  have hρ0 := fun x => (R.positive x).le
  have hU := equilibriumDensityPotential_measurable hρm
  have hw : Measurable (fun x : ℂ => Real.exp (-θ * β * equilibriumDensityPotential R.density x) * R.density x) :=
    (Real.measurable_exp.comp (measurable_const.mul hU)).mul hρm
  have hB : 0 ≤ equilibriumCompactEnvelopeConstant βlo βhi * Real.exp (θ * βhi * equilibriumCompactLogBound βlo) :=
    mul_nonneg (equilibriumCompactEnvelopeConstant_pos hlo (hβlo.trans hβhi)).le (Real.exp_pos _).le
  obtain ⟨hi, hb⟩ := equilibrium_integrable_and_integral_le_of_polynomial_gaussian hw
    (fun x => mul_nonneg (Real.exp_pos _).le (hρ0 x)) (mul_nonneg (by linarith) hhi.le)
    (half_pos hlo) hB (equilibriumReference_potential_weight_envelope hlo hβlo hβhi hθ R)
  have hden : 2 * (βlo / 2) = βlo := by ring
  have hmass : 2 * Real.pi / (βlo / 2) = 4 * Real.pi / βlo := by field_simp <;> ring
  rw [hden, hmass] at hb
  refine ⟨?_, ?_⟩
  · rw [← R.density_measure]
    exact (equilibriumDensityMeasure_integrable_iff hρm hρ0 _).mpr hi
  · rw [← R.density_measure, integral_equilibriumDensityMeasure hρm hρ0]
    have he : (∫ x : ℂ, R.density x * Real.exp (-θ * β * equilibriumDensityPotential R.density x)) =
        ∫ x : ℂ, Real.exp (-θ * β * equilibriumDensityPotential R.density x) * R.density x :=
      integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
    rw [he]
    exact hb

/-- The actual selected thermal references obey all three compact-temperature
bounds in the manuscript, for every real m>=0 and every theta>0. -/
theorem equilibriumConstructedReference_compact_bounds {βlo βhi m θ : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hm : 0 ≤ m) (hθ : 0 < θ) :
    ∃ K : ℝ, ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi),
      let R := equilibriumConstructedReference β (hlo.trans_le hβlo)
      |equilibriumDensityInteraction R.density| +
        (∫ x : ℂ, (1 + ‖x‖) ^ m ∂R.measure) +
        (∫ x : ℂ, Real.exp (-θ * β * equilibriumDensityPotential R.density x) ∂R.measure) ≤ K := by
  refine ⟨2 * equilibriumCompactLogBound βlo + 1 / 2 + equilibriumCompactMomentBound βlo βhi m +
    equilibriumCompactPotentialBound βlo βhi θ, ?_⟩
  intro β hβlo hβhi
  let R := equilibriumConstructedReference β (hlo.trans_le hβlo)
  have hc := equilibriumReference_interaction_abs_bound hlo hβlo R
  have hp := (equilibriumReference_polynomial_moment_bound hlo hβlo hβhi hm R).2
  have he := (equilibriumReference_potential_exponential_bound hlo hβlo hβhi hθ R).2
  linarith

end RepulsiveCoulomb
