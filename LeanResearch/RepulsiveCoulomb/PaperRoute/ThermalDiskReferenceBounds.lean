import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Additive repair source. Validation status is recorded in separate evidence.

Thermal EL normalization by the actual unit disk, followed by an endpoint-only
Gaussian-polynomial envelope and genuine polynomial/potential moments. The
reference is explicitly supplied. The old whole-plane EL-normalizer estimate
and its envelope/moment consumers are not selected by these proof bodies.

This thermal disk is distinct from the point-weight conditional normalizer.
-/
noncomputable section
open MeasureTheory Real Set Filter Metric
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- The unnormalized thermal EL weight on the original physical plane. -/
def paperThermalELWeight {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) : ℝ :=
  Real.exp (-β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential R.density x))

/-- Pointwise EL identifies the weight before any integration is performed. -/
theorem paperThermalELWeight_eq_scaled_density {β : ℝ}
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    paperThermalELWeight R x = Real.exp (-R.elConstant) * R.density x := by
  rw [equilibrium_pointwise_EL_density_eq_exp R.positive R.eulerLagrange x,
    ← Real.exp_add]
  unfold paperThermalELWeight
  congr 1
  ring

/-- Finiteness follows from the literal normalized density, not an integral default. -/
theorem paperThermalELWeight_integrable {β : ℝ} (R : EquilibriumConstructedReference β) :
    Integrable (paperThermalELWeight R) := by
  have he : paperThermalELWeight R = fun x => Real.exp (-R.elConstant) * R.density x :=
    funext (paperThermalELWeight_eq_scaled_density R)
  rw [he]
  exact R.integrable.const_mul _

theorem paperThermalELWeight_integral {β : ℝ} (R : EquilibriumConstructedReference β) :
    (∫ x : ℂ, paperThermalELWeight R x) = Real.exp (-R.elConstant) := by
  simp_rw [paperThermalELWeight_eq_scaled_density]
  rw [integral_const_mul, R.mass_one, mul_one]

/-- The inverse normalizer in the manuscript, derived from EL and mass one. -/
theorem paper_reference_EL_normalizer_inverse {β : ℝ}
    (R : EquilibriumConstructedReference β) :
    Integrable (paperThermalELWeight R) ∧
      0 < (∫ x : ℂ, paperThermalELWeight R x) ∧
      Real.exp R.elConstant = (∫ x : ℂ, paperThermalELWeight R x)⁻¹ := by
  refine ⟨paperThermalELWeight_integrable R, ?_, ?_⟩
  · rw [paperThermalELWeight_integral]
    exact Real.exp_pos _
  · rw [paperThermalELWeight_integral, Real.exp_neg, inv_inv]

/-- Actual restricted-disk lower bound. The disk area pi remains explicit. -/
theorem paper_reference_EL_normalizer_unitDisk_lower {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    Real.pi * Real.exp (-β) ≤
      ∫ x in closedBall (0 : ℂ) 1, paperThermalELWeight R x := by
  let μ : Measure ℂ := volume.restrict (closedBall (0 : ℂ) 1)
  let : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (closedBall (0 : ℂ) 1)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have hv : μ.real univ = Real.pi := by
    simp [μ, Measure.real, Complex.volume_closedBall]
  have hc : IntegrableOn (fun _ : ℂ => Real.exp (-β)) (closedBall (0 : ℂ) 1) :=
    integrable_const (μ := μ) _
  have hw := (paperThermalELWeight_integrable R).integrableOn
    (s := closedBall (0 : ℂ) 1)
  have hlower (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) 1) :
      Real.exp (-β) ≤ paperThermalELWeight R x := by
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hU := equilibriumReference_potential_upper R x
    have hV : ‖x‖ ^ 2 / 2 + equilibriumDensityPotential R.density x ≤ 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hV hβ.le
    apply Real.exp_le_exp.mpr
    change -β ≤ -β * (‖x‖ ^ 2 / 2 + equilibriumDensityPotential R.density x)
    nlinarith
  have h := setIntegral_mono_on hc hw isClosed_closedBall.measurableSet hlower
  change (∫ _ : ℂ, Real.exp (-β) ∂μ) ≤ _ at h
  simpa only [integral_const, hv, smul_eq_mul] using h

/-- The full normalizer is bounded below by its actual unit-disk integral. -/
theorem paper_reference_EL_normalizer_lower {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    Real.pi * Real.exp (-β) ≤ ∫ x : ℂ, paperThermalELWeight R x := by
  exact (paper_reference_EL_normalizer_unitDisk_lower hβ R).trans
    (setIntegral_le_integral (paperThermalELWeight_integrable R)
      (Eventually.of_forall (fun x => (Real.exp_pos _).le)))

/-- The literal unit-disk thermal normalizer estimate, with finite positive integral. -/
theorem paper_reference_EL_normalizer_disk {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    Integrable (paperThermalELWeight R) ∧
      0 < (∫ x : ℂ, paperThermalELWeight R x) ∧
      Real.exp R.elConstant = (∫ x : ℂ, paperThermalELWeight R x)⁻¹ ∧
      Real.exp R.elConstant ≤ Real.exp β / Real.pi := by
  obtain ⟨hi, hp, he⟩ := paper_reference_EL_normalizer_inverse R
  refine ⟨hi, hp, he, ?_⟩
  calc
    Real.exp R.elConstant = (∫ x : ℂ, paperThermalELWeight R x)⁻¹ := he
    _ ≤ (Real.pi * Real.exp (-β))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (mul_pos Real.pi_pos (Real.exp_pos (-β)))
        (paper_reference_EL_normalizer_lower hβ R)
    _ = Real.exp β / Real.pi := by
      rw [Real.exp_neg]
      field_simp [Real.pi_ne_zero, Real.exp_ne_zero β]

/-- Compact-temperature normalization bound, still obtained from the unit disk. -/
theorem paper_reference_exp_elConstant_le_disk {β b : ℝ} (hβ : 0 < β)
    (hβb : β ≤ b) (R : EquilibriumConstructedReference β) :
    Real.exp R.elConstant ≤ Real.exp b / Real.pi :=
  (paper_reference_EL_normalizer_disk hβ R).2.2.2.trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hβb) Real.pi_pos.le)

/-- The endpoint-only envelope constant from exp(C_beta)<=exp(b)/pi. -/
def paperDiskCompactEnvelopeConstant (a b : ℝ) : ℝ :=
  Real.pi⁻¹ * Real.exp (b * (1 + equilibriumCompactLogBound a))

theorem paperDiskCompactEnvelopeConstant_pos (a b : ℝ) :
    0 < paperDiskCompactEnvelopeConstant a b := by
  unfold paperDiskCompactEnvelopeConstant
  exact mul_pos (inv_pos.mpr Real.pi_pos) (Real.exp_pos _)

/-- The EL prefactor now consumes the disk estimate, not the frozen Gaussian estimate. -/
theorem paper_reference_tail_prefactor_bound_disk {β a b : ℝ}
    (ha : 0 < a) (hlo : a ≤ β) (hhi : β ≤ b) (R : EquilibriumConstructedReference β) :
    Real.exp (R.elConstant + β * (∫ y : ℂ, equilibriumLogMoment y * R.density y)) ≤
      paperDiskCompactEnvelopeConstant a b := by
  have hβ : 0 < β := ha.trans_le hlo
  let L : ℝ := ∫ y : ℂ, equilibriumLogMoment y * R.density y
  have hL : L ≤ equilibriumCompactLogBound a := equilibriumReference_logMoment_bound ha hlo R
  have hL0 : 0 ≤ L :=
    integral_nonneg (fun y => mul_nonneg (equilibriumLogMoment_nonneg y) (R.positive y).le)
  have hprod : β * L ≤ b * equilibriumCompactLogBound a :=
    mul_le_mul hhi hL hL0 (ha.trans_le (hlo.trans hhi)).le
  have hC := paper_reference_exp_elConstant_le_disk hβ hhi R
  calc
    Real.exp (R.elConstant + β * L) = Real.exp R.elConstant * Real.exp (β * L) :=
      Real.exp_add _ _
    _ ≤ (Real.exp b / Real.pi) * Real.exp (β * L) :=
      mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ ≤ (Real.exp b / Real.pi) * Real.exp (b * equilibriumCompactLogBound a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hprod) (by positivity)
    _ = paperDiskCompactEnvelopeConstant a b := by
      unfold paperDiskCompactEnvelopeConstant
      rw [div_eq_mul_inv]
      rw [show Real.exp b * Real.pi⁻¹ * Real.exp (b * equilibriumCompactLogBound a) =
        Real.pi⁻¹ * (Real.exp b * Real.exp (b * equilibriumCompactLogBound a)) by ring,
        ← Real.exp_add]
      congr 2
      ring

/-- The original compact Gaussian-polynomial envelope, with the disk edge selected. -/
theorem paper_reference_uniform_envelope_disk {β a b : ℝ}
    (ha : 0 < a) (hlo : a ≤ β) (hhi : β ≤ b)
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    R.density x ≤ paperDiskCompactEnvelopeConstant a b *
      equilibriumPolynomialGaussian b (a / 2) x := by
  have hβ : 0 < β := ha.trans_le hlo
  have htail := equilibrium_EL_polynomial_gaussian_bound hβ (R.positive x) x (R.eulerLagrange x)
    (equilibriumReference_potential_lower R x)
  have hA := paper_reference_tail_prefactor_bound_disk ha hlo hhi R
  have hB0 := (paperDiskCompactEnvelopeConstant_pos a b).le
  have hp : (1 + ‖x‖) ^ β ≤ (1 + ‖x‖) ^ b :=
    Real.rpow_le_rpow_of_exponent_le (by have := norm_nonneg x; linarith) hhi
  have he : Real.exp (-β * ‖x‖ ^ 2 / 2) ≤ Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖x‖)
    nlinarith
  have hh := mul_le_mul hA hp (Real.rpow_nonneg (by positivity) _) hB0
  have h := mul_le_mul hh he (Real.exp_pos _).le
    (mul_nonneg hB0 (Real.rpow_nonneg (by positivity) _))
  apply htail.trans
  simpa only [equilibriumPolynomialGaussian, mul_assoc] using h

def paperDiskCompactMomentBound (βlo βhi m : ℝ) : ℝ :=
  paperDiskCompactEnvelopeConstant βlo βhi * Real.exp ((m + βhi) ^ 2 / βlo) * (4 * Real.pi / βlo)

def paperDiskCompactPotentialBound (βlo βhi θ : ℝ) : ℝ :=
  (paperDiskCompactEnvelopeConstant βlo βhi * Real.exp (θ * βhi * equilibriumCompactLogBound βlo)) *
    Real.exp (((1 + θ) * βhi) ^ 2 / βlo) * (4 * Real.pi / βlo)

/-- Positivity of the explicit moment constants requires only the temperature floor. -/
theorem paperDiskCompactMomentBound_pos {a : ℝ} (ha : 0 < a) (b m : ℝ) :
    0 < paperDiskCompactMomentBound a b m := by
  unfold paperDiskCompactMomentBound
  exact mul_pos
    (mul_pos (paperDiskCompactEnvelopeConstant_pos a b) (Real.exp_pos _))
    (div_pos (mul_pos (by norm_num) Real.pi_pos) ha)

theorem paperDiskCompactPotentialBound_pos {a : ℝ} (ha : 0 < a) (b θ : ℝ) :
    0 < paperDiskCompactPotentialBound a b θ := by
  unfold paperDiskCompactPotentialBound
  exact mul_pos
    (mul_pos (mul_pos (paperDiskCompactEnvelopeConstant_pos a b) (Real.exp_pos _))
      (Real.exp_pos _))
    (div_pos (mul_pos (by norm_num) Real.pi_pos) ha)

/-- Every real polynomial moment is actually integrable, with one uniform
bound on the compact beta interval. -/
theorem paper_reference_polynomial_moment_bound_disk {β βlo βhi m : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) (hm : 0 ≤ m)
    (R : EquilibriumConstructedReference β) :
    Integrable (fun x : ℂ => (1 + ‖x‖) ^ m) R.measure ∧
      (∫ x : ℂ, (1 + ‖x‖) ^ m ∂R.measure) ≤ paperDiskCompactMomentBound βlo βhi m := by
  have hhi : 0 < βhi := hlo.trans_le (hβlo.trans hβhi)
  have hB := (paperDiskCompactEnvelopeConstant_pos βlo βhi).le
  have hρm := R.smooth.continuous.measurable
  have hρ0 := fun x => (R.positive x).le
  have hw : Measurable (fun x : ℂ => (1 + ‖x‖) ^ m * R.density x) :=
    (((Real.continuous_rpow_const hm).comp (continuous_const.add continuous_norm)).measurable).mul hρm
  have hbound (x : ℂ) : (1 + ‖x‖) ^ m * R.density x ≤
      paperDiskCompactEnvelopeConstant βlo βhi * equilibriumPolynomialGaussian (m + βhi) (βlo / 2) x := by
    have h := mul_le_mul_of_nonneg_left (paper_reference_uniform_envelope_disk hlo hβlo hβhi R x)
      (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) m)
    apply h.trans_eq
    unfold equilibriumPolynomialGaussian
    rw [Real.rpow_add (by positivity : 0 < 1 + ‖x‖)]
    ring
  obtain ⟨hi, hb⟩ := equilibrium_integrable_and_integral_le_of_polynomial_gaussian hw
    (fun x => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hρ0 x))
    (add_nonneg hm hhi.le) (half_pos hlo) hB hbound
  have hden : 2 * (βlo / 2) = βlo := by ring
  have hmass : 2 * Real.pi / (βlo / 2) = 4 * Real.pi / βlo := by field_simp; ring
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
theorem paper_reference_potential_weight_envelope_disk {β βlo βhi θ : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) (hθ : 0 < θ)
    (R : EquilibriumConstructedReference β) (x : ℂ) :
    Real.exp (-θ * β * equilibriumDensityPotential R.density x) * R.density x ≤
      (paperDiskCompactEnvelopeConstant βlo βhi * Real.exp (θ * βhi * equilibriumCompactLogBound βlo)) *
        equilibriumPolynomialGaussian ((1 + θ) * βhi) (βlo / 2) x := by
  have hβ : 0 < β := hlo.trans_le hβlo
  have hhi : 0 < βhi := hβ.trans_le hβhi
  have hB := (paperDiskCompactEnvelopeConstant_pos βlo βhi).le
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
        (paperDiskCompactEnvelopeConstant βlo βhi * equilibriumPolynomialGaussian βhi (βlo / 2) x) :=
      mul_le_mul_of_nonneg_left (paper_reference_uniform_envelope_disk hlo hβlo hβhi R x) (Real.exp_pos _).le
    _ = paperDiskCompactEnvelopeConstant βlo βhi *
        (Real.exp (-θ * β * equilibriumDensityPotential R.density x) * (1 + ‖x‖) ^ βhi) *
          Real.exp (-(βlo / 2) * ‖x‖ ^ 2) := by unfold equilibriumPolynomialGaussian; ring
    _ ≤ paperDiskCompactEnvelopeConstant βlo βhi *
        (Real.exp (θ * βhi * equilibriumCompactLogBound βlo) * (1 + ‖x‖) ^ ((1 + θ) * βhi)) *
          Real.exp (-(βlo / 2) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hB) (Real.exp_pos _).le
    _ = _ := by unfold equilibriumPolynomialGaussian; ring

/-- Actual exponential-potential integrability and its compact-beta bound. -/
theorem paper_reference_potential_exponential_bound_disk {β βlo βhi θ : ℝ}
    (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) (hθ : 0 < θ)
    (R : EquilibriumConstructedReference β) :
    Integrable (fun x : ℂ => Real.exp (-θ * β * equilibriumDensityPotential R.density x)) R.measure ∧
      (∫ x : ℂ, Real.exp (-θ * β * equilibriumDensityPotential R.density x) ∂R.measure) ≤
        paperDiskCompactPotentialBound βlo βhi θ := by
  have hhi : 0 < βhi := hlo.trans_le (hβlo.trans hβhi)
  have hρm := R.smooth.continuous.measurable
  have hρ0 := fun x => (R.positive x).le
  have hU := equilibriumDensityPotential_measurable hρm
  have hw : Measurable (fun x : ℂ => Real.exp (-θ * β * equilibriumDensityPotential R.density x) * R.density x) :=
    (Real.measurable_exp.comp (measurable_const.mul hU)).mul hρm
  have hB : 0 ≤ paperDiskCompactEnvelopeConstant βlo βhi * Real.exp (θ * βhi * equilibriumCompactLogBound βlo) :=
    mul_nonneg (paperDiskCompactEnvelopeConstant_pos βlo βhi).le (Real.exp_pos _).le
  obtain ⟨hi, hb⟩ := equilibrium_integrable_and_integral_le_of_polynomial_gaussian hw
    (fun x => mul_nonneg (Real.exp_pos _).le (hρ0 x)) (mul_nonneg (by linarith) hhi.le)
    (half_pos hlo) hB (paper_reference_potential_weight_envelope_disk hlo hβlo hβhi hθ R)
  have hden : 2 * (βlo / 2) = βlo := by ring
  have hmass : 2 * Real.pi / (βlo / 2) = 4 * Real.pi / βlo := by field_simp; ring
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


/-- One explicit bound is fixed before beta and every supplied reference.
No selected thermal constructor or continuity of a reference family is used. -/
theorem paper_reference_compact_bounds_disk {a b m θ : ℝ}
    (ha : 0 < a) (_hab : a ≤ b) (hm : 0 ≤ m) (hθ : 0 < θ) :
    ∃ K : ℝ, ∀ β (_hlo : a ≤ β) (_hhi : β ≤ b),
      ∀ R : EquilibriumConstructedReference β,
      |equilibriumDensityInteraction R.density| +
        (∫ x : ℂ, (1 + ‖x‖) ^ m ∂R.measure) +
        (∫ x : ℂ, Real.exp (-θ * β * equilibriumDensityPotential R.density x) ∂R.measure) ≤ K := by
  refine ⟨2 * equilibriumCompactLogBound a + 1 / 2 +
    paperDiskCompactMomentBound a b m + paperDiskCompactPotentialBound a b θ, ?_⟩
  intro β hlo hhi R
  have hc := equilibriumReference_interaction_abs_bound ha hlo R
  have hp := (paper_reference_polynomial_moment_bound_disk ha hlo hhi hm R).2
  have he := (paper_reference_potential_exponential_bound_disk ha hlo hhi hθ R).2
  linarith

end RepulsiveCoulomb.PaperRoute
