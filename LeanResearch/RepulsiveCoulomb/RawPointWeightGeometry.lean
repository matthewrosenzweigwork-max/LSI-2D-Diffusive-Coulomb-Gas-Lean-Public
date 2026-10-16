import LeanResearch.RepulsiveCoulomb.PointConstantDomain
import LeanResearch.RepulsiveCoulomb.PointWeightAnnularNormalization
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-! Uniform local geometry of the raw product weight. This module starts with
literal weights and elementary local bounds. It does not postulate a strong-A-infinity
or weighted Poincare theorem. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointWeight {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  ∏ j, ‖z - y j‖ ^ a j

theorem rawPointWeight_eq_pointWeight_zero {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    rawPointWeight a y = pointWeight 0 a y := by
  funext z
  simp [rawPointWeight, pointWeight]

theorem rawPointWeight_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) :
    0 ≤ rawPointWeight a y z :=
  Finset.prod_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

theorem rawPointWeight_continuous {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) : Continuous (rawPointWeight a y) := by
  rw [rawPointWeight_eq_pointWeight_zero]
  exact pointWeight_continuous 0 ha y

/-- A local size factor depending on radius and distances to the center. -/
def rawPointBallFactor {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  ∏ j, (r + ‖c - y j‖) ^ a j

theorem rawPointWeight_le_ballFactor {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (c : ℂ) (r : ℝ) {z : ℂ} (hz : z ∈ closedBall c r) :
    rawPointWeight a y z ≤ rawPointBallFactor a y c r := by
  apply Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
  intro j _
  apply Real.rpow_le_rpow (norm_nonneg _) _ (ha j)
  have hd : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  calc
    ‖z - y j‖ = ‖(z - c) + (c - y j)‖ := by congr 1; ring
    _ ≤ ‖z - c‖ + ‖c - y j‖ := norm_add_le _ _
    _ ≤ r + ‖c - y j‖ := by linarith

theorem rawPointWeight_ball_integrable {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (c : ℂ) (r : ℝ) :
    IntegrableOn (rawPointWeight a y) (closedBall c r) :=
  (rawPointWeight_continuous ha y).continuousOn.integrableOn_compact (isCompact_closedBall c r)

theorem rawPointWeight_ball_integral_upper {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ z in closedBall c r, rawPointWeight a y z) ≤
      Real.pi * r ^ 2 * rawPointBallFactor a y c r := by
  have hb := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℂ))
    (f := rawPointWeight a y) (C := rawPointBallFactor a y c r)
    (isCompact_closedBall c r).measure_lt_top (fun z hz ↦ ?_)
  · have hv : volume.real (closedBall c r) = r ^ 2 * Real.pi := by
      simp [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr]
    calc
      _ ≤ ‖∫ z in closedBall c r, rawPointWeight a y z‖ := le_abs_self _
      _ ≤ rawPointBallFactor a y c r * volume.real (closedBall c r) := hb
      _ = _ := by rw [hv]; ring
  · rw [Real.norm_eq_abs, abs_of_nonneg (rawPointWeight_nonneg a y z)]
    exact rawPointWeight_le_ballFactor ha y c r hz

/-- Exact centered rescaling; the exponent sum is retained without a separation hypothesis. -/
theorem rawPointWeight_affine_rescaling {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    rawPointWeight a y (c + r • z) = r ^ (∑ j, a j) *
      rawPointWeight a (fun j ↦ r⁻¹ • (y j - c)) z := by
  have he (j : Fin m) : c + r • z - y j = r • (z - r⁻¹ • (y j - c)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  unfold rawPointWeight
  simp_rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    Real.mul_rpow hr.le (norm_nonneg _)]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr]

theorem complex_lintegral_polar (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ, f z) = ∫⁻ R in Ioi (0 : ℝ), ENNReal.ofReal R *
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ)) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  simp only [smul_eq_mul, polarCoord_target]
  change (∫⁻ p : ℝ × ℝ, ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)
      ∂(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _
  rw [← Measure.prod_restrict]
  have hm : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)) :=
    measurable_fst.ennreal_ofReal.mul (hf.comp continuous_complex_polarCoord_symm.measurable)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro R
  exact lintegral_const_mul (ENNReal.ofReal R) (hf.comp (continuous_complex_polarCoord_symm.comp
    (continuous_const.prodMk continuous_id)).measurable)

theorem pointWeight_le_raw {m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) :
    pointWeight γ a y z ≤ rawPointWeight a y z := by
  have he : Real.exp (-γ * ‖z‖ ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hγ (sq_nonneg ‖z‖)])
  exact mul_le_of_le_one_left (rawPointWeight_nonneg a y z) he

/-- A lower bound on the fixed ball, with a constant chosen before the configuration. -/
theorem rawPointWeight_ball_two_lower {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    ENNReal.ofReal (pointLowerConstant 1 Q * pointLocationFactor a y) ≤
      ∫⁻ z in closedBall (0 : ℂ) 2, ENNReal.ofReal (rawPointWeight a y z) := by
  let f : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) 2).indicator (fun z ↦ ENNReal.ofReal (rawPointWeight a y z))
  have hf : Measurable f := ((rawPointWeight_continuous ha y).measurable.ennreal_ofReal).indicator isClosed_closedBall.measurableSet
  have havoid : ∀ᵐ R : ℝ, ∀ j, R ≠ ‖y j‖ :=
    ae_all_iff.mpr fun j ↦ volume.ae_ne (‖y j‖)
  have hpoint : ∀ᵐ R ∂volume.restrict (Ioc (1 : ℝ) 2),
      ENNReal.ofReal (pointLowerConstant 1 Q * pointLocationFactor a y) ≤
        ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae havoid] with R hR hav
    have hc := pointWeight_circleAverage_lower (by norm_num : (0 : ℝ) < 1) ha hQ y hR.1.le hR.2 hav
    have hg : ENNReal.ofReal (pointLowerConstant 1 Q * pointLocationFactor a y) ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (pointWeight 1 a y (Complex.polarCoord.symm (R, θ))) := by
      rw [angularLIntegral_eq_circleAverage _ (pointWeight_continuous 1 ha y) (pointWeight_nonneg 1 a y)]
      apply ENNReal.ofReal_le_ofReal
      exact (by simpa only [pointLowerConstant, mul_assoc] using mul_le_mul_of_nonneg_left hc Real.two_pi_pos.le)
    have hm : (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (pointWeight 1 a y (Complex.polarCoord.symm (R, θ)))) ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ)) := by
      apply lintegral_mono
      intro θ
      have hn : ‖Complex.polarCoord.symm (R, θ)‖ = R := by
        rw [polarCoord_symm_eq_circleMap]
        rw [norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hR.1)]
      have hz : Complex.polarCoord.symm (R, θ) ∈ closedBall (0 : ℂ) 2 := by
        simpa only [mem_closedBall, dist_zero_right, hn] using hR.2
      dsimp only [f]
      rw [Set.indicator_of_mem hz]
      exact ENNReal.ofReal_le_ofReal (pointWeight_le_raw (by norm_num) a y _)
    have hR' : (1 : ENNReal) ≤ ENNReal.ofReal R := by
      simpa using ENNReal.ofReal_le_ofReal hR.1.le
    apply (hg.trans hm).trans
    calc
      _ = 1 * (∫⁻ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ))) := (one_mul _).symm
      _ ≤ _ := by gcongr
  calc
    _ = ∫⁻ R in Ioc (1 : ℝ) 2, ENNReal.ofReal (pointLowerConstant 1 Q * pointLocationFactor a y) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      norm_num
    _ ≤ ∫⁻ R in Ioc (1 : ℝ) 2, ENNReal.ofReal R *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ)) := lintegral_mono_ae hpoint
    _ ≤ ∫⁻ R in Ioi (0 : ℝ), ENNReal.ofReal R *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (R, θ)) :=
      lintegral_mono_set (fun R hR ↦ lt_trans zero_lt_one hR.1)
    _ = ∫⁻ z, f z := (complex_lintegral_polar f hf).symm
    _ = _ := lintegral_indicator isClosed_closedBall.measurableSet _

theorem complex_integral_affine (f : ℂ → ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z : ℂ, f (c + r • z)) = (r ^ 2)⁻¹ * ∫ z : ℂ, f z := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
    (fun z ↦ f (c + z)) r (hR := hr.le)
  simpa only [Complex.finrank_real_complex, smul_eq_mul, integral_add_left_eq_self] using h

theorem rawPointWeight_ball_rescaling {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall c (2 * r), rawPointWeight a y z) =
      r ^ 2 * r ^ (∑ j, a j) *
        ∫ z in closedBall (0 : ℂ) 2, rawPointWeight a (fun j ↦ r⁻¹ • (y j - c)) z := by
  let f : ℂ → ℝ := (closedBall c (2 * r)).indicator (rawPointWeight a y)
  have hmem (z : ℂ) : c + r • z ∈ closedBall c (2 * r) ↔ z ∈ closedBall (0 : ℂ) 2 := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor <;> intro h <;> nlinarith
  have he (z : ℂ) : f (c + r • z) = r ^ (∑ j, a j) *
      (closedBall (0 : ℂ) 2).indicator (rawPointWeight a (fun j ↦ r⁻¹ • (y j - c))) z := by
    by_cases hz : z ∈ closedBall (0 : ℂ) 2
    · simp only [f, Set.indicator_of_mem hz, Set.indicator_of_mem ((hmem z).mpr hz)]
      exact rawPointWeight_affine_rescaling a y c hr z
    · simp only [f, Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (fun h ↦ hz ((hmem z).mp h)), mul_zero]
  have hi := complex_integral_affine f c hr
  simp_rw [he] at hi
  rw [integral_const_mul, integral_indicator isClosed_closedBall.measurableSet] at hi
  change r ^ (∑ j, a j) * (∫ z in closedBall (0 : ℂ) 2,
      rawPointWeight a (fun j ↦ r⁻¹ • (y j - c)) z) = (r ^ 2)⁻¹ *
      (∫ z, (closedBall c (2 * r)).indicator (rawPointWeight a y) z) at hi
  rw [integral_indicator isClosed_closedBall.measurableSet] at hi
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  field_simp at hi
  simpa only [one_div, mul_comm, mul_left_comm, mul_assoc] using hi.symm

theorem rawPointBallFactor_rescaling {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    r ^ (∑ j, a j) * pointLocationFactor a (fun j ↦ r⁻¹ • (y j - c)) =
      rawPointBallFactor a y c r := by
  unfold pointLocationFactor rawPointBallFactor
  rw [Real.rpow_sum_of_pos hr, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Real.mul_rpow hr.le (by positivity)]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), norm_sub_rev]
  field_simp

theorem rawPointWeight_ball_two_lower_real {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    pointLowerConstant 1 Q * pointLocationFactor a y ≤
      ∫ z in closedBall (0 : ℂ) 2, rawPointWeight a y z := by
  have h := rawPointWeight_ball_two_lower ha hQ y
  rw [← ofReal_integral_eq_lintegral_ofReal (rawPointWeight_ball_integrable ha y 0 2)
    (Eventually.of_forall (rawPointWeight_nonneg a y))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (rawPointWeight_nonneg a y))).mp h

theorem rawPointWeight_ball_integral_lower {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    pointLowerConstant 1 Q * r ^ 2 * rawPointBallFactor a y c r ≤
      ∫ z in closedBall c (2 * r), rawPointWeight a y z := by
  rw [rawPointWeight_ball_rescaling a y c hr]
  have h := mul_le_mul_of_nonneg_left
    (rawPointWeight_ball_two_lower_real ha hQ (fun j ↦ r⁻¹ • (y j - c)))
    (mul_nonneg (sq_nonneg r) (Real.rpow_nonneg hr.le (∑ j, a j)))
  calc
    _ = (r ^ 2 * r ^ (∑ j, a j)) *
        (pointLowerConstant 1 Q * pointLocationFactor a (fun j ↦ r⁻¹ • (y j - c))) := by
      rw [← rawPointBallFactor_rescaling a y c hr]
      ring
    _ ≤ _ := h

theorem rawPointBallFactor_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ rawPointBallFactor a y c r :=
  Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (by positivity) _

theorem rawPointBallFactor_dilate {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 1 ≤ s) :
    rawPointBallFactor a y c (s * r) ≤ s ^ Q * rawPointBallFactor a y c r := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hp : rawPointBallFactor a y c (s * r) ≤
      (s ^ (∑ j, a j)) * rawPointBallFactor a y c r := by
    unfold rawPointBallFactor
    rw [Real.rpow_sum_of_pos hs0, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (by positivity) _)
    intro j _
    rw [← Real.mul_rpow hs0.le (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (ha j)
    nlinarith [norm_nonneg (c - y j)]
  exact hp.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hs hQ) (rawPointBallFactor_nonneg a y c hr))

def rawPointDoublingConstant (Q : ℝ) : ℝ :=
  16 * Real.pi * (4 : ℝ) ^ Q / pointLowerConstant 1 Q

theorem rawPointDoublingConstant_pos (Q : ℝ) : 0 < rawPointDoublingConstant Q := by
  unfold rawPointDoublingConstant
  exact div_pos (by positivity) (pointLowerConstant_pos 1 Q)

/-- Configuration-uniform doubling in integral form, at every center and positive radius. -/
theorem rawPointWeight_doubling {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall c (2 * r), rawPointWeight a y z) ≤
      rawPointDoublingConstant Q * ∫ z in closedBall c r, rawPointWeight a y z := by
  have hf := rawPointBallFactor_dilate ha hQ y c (r := r / 2) (s := 4) (by positivity) (by norm_num)
  have he : 4 * (r / 2) = 2 * r := by ring
  rw [he] at hf
  have hl := rawPointWeight_ball_integral_lower ha hQ y c (r := r / 2) (by positivity)
  have he2 : 2 * (r / 2) = r := by ring
  rw [he2] at hl
  calc
    _ ≤ Real.pi * (2 * r) ^ 2 * rawPointBallFactor a y c (2 * r) :=
      rawPointWeight_ball_integral_upper ha y c (by positivity)
    _ ≤ Real.pi * (2 * r) ^ 2 * ((4 : ℝ) ^ Q * rawPointBallFactor a y c (r / 2)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = rawPointDoublingConstant Q *
        (pointLowerConstant 1 Q * (r / 2) ^ 2 * rawPointBallFactor a y c (r / 2)) := by
      unfold rawPointDoublingConstant
      field_simp [ne_of_gt (pointLowerConstant_pos 1 Q)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (rawPointDoublingConstant_pos Q).le

def rawPointMeasure {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Measure ℂ :=
  volume.withDensity (fun z ↦ ENNReal.ofReal (rawPointWeight a y z))

theorem rawPointMeasure_closedBall {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (c : ℂ) (r : ℝ) :
    rawPointMeasure a y (closedBall c r) = ENNReal.ofReal (∫ z in closedBall c r, rawPointWeight a y z) := by
  rw [rawPointMeasure, withDensity_apply _ isClosed_closedBall.measurableSet]
  exact (ofReal_integral_eq_lintegral_ofReal (rawPointWeight_ball_integrable ha y c r)
    (Eventually.of_forall (rawPointWeight_nonneg a y))).symm

theorem rawPointMeasure_doubling {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    rawPointMeasure a y (closedBall c (2 * r)) ≤
      ENNReal.ofReal (rawPointDoublingConstant Q) * rawPointMeasure a y (closedBall c r) := by
  rw [rawPointMeasure_closedBall ha y c (2 * r), rawPointMeasure_closedBall ha y c r,
    ← ENNReal.ofReal_mul (rawPointDoublingConstant_pos Q).le]
  exact ENNReal.ofReal_le_ofReal (rawPointWeight_doubling ha hQ y c hr)

end RepulsiveCoulomb
