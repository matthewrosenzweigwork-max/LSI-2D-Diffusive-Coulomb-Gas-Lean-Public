import LeanResearch.RepulsiveCoulomb.PaperRoute.MetricDoublingComparison
import LeanResearch.RepulsiveCoulomb.PaperRoute.SignedAreaBall
import LeanResearch.RepulsiveCoulomb.PaperRoute.WeakQuasisymmetryGeometry
import LeanResearch.RepulsiveCoulomb.PaperRoute.QCWeakQuasisymmetry
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Same-map Semmes metric doubling from signed area and weak quasisymmetry

The measure is literally volume.withDensity of the positive part of the actual
signed real Jacobian. Actual area transport and the image-ball inclusions prove
finite positive balls, doubling, and comparison of the exact midpoint-diameter
ball gauge with the genuine pullback metric of the supplied homeomorphism.
The analytic QC corollary produces weak quasisymmetry rather than assuming it.
A bounded a.e. change of density preserves this same metric with constants
C^2 D and sqrt(C) A. No raw weighted path metric or null-set path transfer is
asserted. No old radial, grid, or Poincare producer enters this proof.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Literal actual-Jacobian density measure. -/
def jacobianMeasure (F : ℂ → ℂ) : Measure ℂ := weightMeasure (signedJacobian F)

/-- Quantitative Jacobian doubling constant, depending only on weak QS. -/
def semmesDoublingConstant (H : ℝ) : ℝ := H ^ 2 * weakQSTwoScale H ^ 2

/-- One common positive constant for both same-map gauge inequalities. -/
def semmesGaugeConstant (H : ℝ) : ℝ :=
  Real.sqrt Real.pi * H ^ 2 + weakQSTwoScale H / Real.sqrt Real.pi

variable (F : ℂ ≃ₜ ℂ)
  (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
  (hJ : ∀ᵐ x ∂volume, 0 < signedJacobian F x)
include hLocal hJ

/-- The actual signed-Jacobian mass equals actual image area, for every radius. -/
theorem jacobianMeasure_ball_eq_volume_image (c : ℂ) (r : ℝ) :
    jacobianMeasure F (ball c r) = volume (F '' ball c r) := by
  obtain ⟨L, hL⟩ := exists_lipschitzOn_ball_of_closedBall hLocal c r
  rw [jacobianMeasure, weightMeasure, withDensity_apply _ measurableSet_ball]
  exact (volume_image_ball_eq_lintegral_signedJacobian hL F.injective.injOn
    (ae_restrict_of_ae hJ)).symm

/-- Finiteness is proved by the actual local Lipschitz image bound. -/
theorem jacobianMeasure_ball_lt_top (c : ℂ) (r : ℝ) :
    jacobianMeasure F (ball c r) < ⊤ := by
  rw [jacobianMeasure_ball_eq_volume_image F hLocal hJ]
  obtain ⟨L, hL⟩ := exists_lipschitzOn_ball_of_closedBall hLocal c r
  exact volume_image_ball_lt_top_of_lipschitzOn hL

omit hLocal hJ in
private theorem volume_complex_ball (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball c r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le,
    ENNReal.ofReal_pow hr]
  simp [ENNReal.ofReal_coe_nnreal, ← NNReal.coe_real_pi, mul_comm]

omit hLocal hJ in
private theorem volume_complex_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall c r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_closedBall, ← Complex.volume_ball]
  exact volume_complex_ball c hr

variable {H : ℝ} (hQS : WeakQuasisymmetricWith F H)
include hQS

/-- Weak QS image inclusions become actual Jacobian ball mass bounds. -/
theorem jacobianMeasure_ball_bounds {c y : ℂ} {r : ℝ} (hy : dist c y = r) :
    ENNReal.ofReal (Real.pi * (dist (F c) (F y) / H) ^ 2) ≤
        jacobianMeasure F (ball c r) ∧
    jacobianMeasure F (ball c r) ≤
        ENNReal.ofReal (Real.pi * (H * dist (F c) (F y)) ^ 2) := by
  rw [jacobianMeasure_ball_eq_volume_image F hLocal hJ]
  have hb := hQS.image_ball_inclusions F.surjective hy
  constructor
  · rw [← volume_complex_ball (F c) (div_nonneg dist_nonneg hQS.constant_pos.le)]
    exact measure_mono hb.1
  · rw [← volume_complex_closedBall (F c) (mul_nonneg hQS.constant_pos.le dist_nonneg)]
    exact measure_mono hb.2

/-- The double ball is controlled by the same source boundary reference. -/
theorem jacobianMeasure_doubleBall_le {c y : ℂ} {r : ℝ} (hy : dist c y = r) :
    jacobianMeasure F (ball c (2 * r)) ≤
      ENNReal.ofReal (Real.pi * (weakQSTwoScale H * dist (F c) (F y)) ^ 2) := by
  rw [jacobianMeasure_ball_eq_volume_image F hLocal hJ,
    ← volume_complex_closedBall (F c) (mul_nonneg hQS.twoScale_pos.le dist_nonneg)]
  apply measure_mono
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_closedBall, dist_comm]
  apply hQS.factor_two
  rw [hy]
  exact (by simpa only [mem_ball, dist_comm] using hz : dist c z < 2 * r).le

omit hLocal hJ hQS in
private theorem dist_boundary_reference (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    dist c (c + (r : ℂ)) = r := by
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

/-- Positive finite mass on every positive-radius Euclidean ball. -/
theorem jacobianMeasure_positiveFiniteBalls : PositiveFiniteBalls (jacobianMeasure F) := by
  intro c r hr
  have hy := dist_boundary_reference c hr.le
  have hcy : c ≠ c + (r : ℂ) := by
    intro heq
    rw [← heq, dist_self] at hy
    linarith
  have hs : 0 < dist (F c) (F (c + (r : ℂ))) :=
    dist_pos.mpr (fun heq => hcy (F.injective heq))
  exact ⟨(ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos
    (div_pos hs hQS.constant_pos)))).trans_le
      (jacobianMeasure_ball_bounds F hLocal hJ hQS hy).1,
    jacobianMeasure_ball_lt_top F hLocal hJ c r⟩

/-- Doubling is derived from inner and doubled outer image balls. -/
theorem jacobianMeasure_globalDoubling :
    GlobalDoublingWith (jacobianMeasure F) (semmesDoublingConstant H) := by
  have hH := hQS.constant_pos
  have hT := hQS.twoScale_pos
  have hT1 : 1 ≤ weakQSTwoScale H := by
    dsimp [weakQSTwoScale]
    nlinarith [hQS.one_le]
  refine ⟨?_, ?_⟩
  · dsimp [semmesDoublingConstant]
    have hh : 1 ≤ H ^ 2 := by nlinarith [hQS.one_le]
    have ht : 1 ≤ weakQSTwoScale H ^ 2 := by nlinarith
    nlinarith
  · intro c r hr
    let y : ℂ := c + (r : ℂ)
    have hy : dist c y = r := dist_boundary_reference c hr.le
    have hlo := (jacobianMeasure_ball_bounds F hLocal hJ hQS hy).1
    calc
      jacobianMeasure F (ball c (2 * r)) ≤
          ENNReal.ofReal (Real.pi * (weakQSTwoScale H * dist (F c) (F y)) ^ 2) :=
        jacobianMeasure_doubleBall_le F hLocal hJ hQS hy
      _ = ENNReal.ofReal (semmesDoublingConstant H) *
          ENNReal.ofReal (Real.pi * (dist (F c) (F y) / H) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by unfold semmesDoublingConstant; positivity : 0 ≤ semmesDoublingConstant H)]
        congr 1
        dsimp [semmesDoublingConstant]
        field_simp
      _ ≤ ENNReal.ofReal (semmesDoublingConstant H) * jacobianMeasure F (ball c r) :=
        mul_le_mul_right hlo _

/-- Real square-root mass bounds, with all toReal conversions justified. -/
theorem sqrt_jacobianMeasure_ball_bounds {c y : ℂ} {r : ℝ} (hy : dist c y = r) :
    Real.sqrt Real.pi * (dist (F c) (F y) / H) ≤
        Real.sqrt (jacobianMeasure F (ball c r)).toReal ∧
    Real.sqrt (jacobianMeasure F (ball c r)).toReal ≤
        Real.sqrt Real.pi * (H * dist (F c) (F y)) := by
  have hb := jacobianMeasure_ball_bounds F hLocal hJ hQS hy
  have hl := ENNReal.toReal_mono (jacobianMeasure_ball_lt_top F hLocal hJ c r).ne hb.1
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.2
  rw [ENNReal.toReal_ofReal (by positivity)] at hl hu
  constructor
  · simpa only [Real.sqrt_mul Real.pi_pos.le,
      Real.sqrt_sq (div_nonneg dist_nonneg hQS.constant_pos.le)] using Real.sqrt_le_sqrt hl
  · simpa only [Real.sqrt_mul Real.pi_pos.le,
      Real.sqrt_sq (mul_nonneg hQS.constant_pos.le dist_nonneg)] using Real.sqrt_le_sqrt hu

omit hLocal hJ hQS in
private theorem complex_midpoint_eq (x y : ℂ) : midpoint ℝ x y = (x + y) / 2 := by
  rw [midpoint_eq_smul_add]
  simp
  ring

/-- Comparison with the literal same-map pullback metric and exact diameter ball. -/
theorem jacobianMeasure_gaugeComparable :
    GaugeComparable (jacobianMeasure F) (pullbackMetric F) (semmesGaugeConstant H) := by
  have hH := hQS.constant_pos
  have hT := hQS.twoScale_pos
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hA : 0 < semmesGaugeConstant H := by
    unfold semmesGaugeConstant
    positivity
  refine ⟨hA, ?_⟩
  intro x y
  change diameterGauge (jacobianMeasure F) x y / semmesGaugeConstant H ≤ dist (F x) (F y) ∧
    dist (F x) (F y) ≤ semmesGaugeConstant H * diameterGauge (jacobianMeasure F) x y
  by_cases hxy : x = y
  · subst y
    simp
  let c : ℂ := (x + y) / 2
  have hcx : dist c x = dist x y / 2 := by
    dsimp [c]
    rw [← complex_midpoint_eq]
    simp [dist_midpoint_left, div_eq_mul_inv, mul_comm]
  have hcy : dist c y = dist x y / 2 := by
    dsimp [c]
    rw [← complex_midpoint_eq]
    simp [dist_midpoint_right, div_eq_mul_inv, mul_comm]
  have hs : dist (F c) (F x) ≤ H * dist (F x) (F y) := by
    rw [dist_comm]
    apply hQS.control
    rw [dist_comm x c, hcx]
    linarith [dist_nonneg (x := x) (y := y)]
  have hd : dist (F x) (F y) ≤ (1 + H) * dist (F c) (F x) := by
    have hy := hQS.control c y x (by rw [hcx, hcy])
    have ht := dist_triangle (F x) (F c) (F y)
    rw [dist_comm (F x) (F c)] at ht
    nlinarith
  obtain ⟨hblo, hbup⟩ := sqrt_jacobianMeasure_ball_bounds F hLocal hJ hQS hcx
  change Real.sqrt Real.pi * (dist (F c) (F x) / H) ≤
      diameterGauge (jacobianMeasure F) x y at hblo
  change diameterGauge (jacobianMeasure F) x y ≤
      Real.sqrt Real.pi * (H * dist (F c) (F x)) at hbup
  have hlo : diameterGauge (jacobianMeasure F) x y ≤
      (Real.sqrt Real.pi * H ^ 2) * dist (F x) (F y) := by
    calc
      _ ≤ Real.sqrt Real.pi * (H * dist (F c) (F x)) := hbup
      _ ≤ Real.sqrt Real.pi * (H * (H * dist (F x) (F y))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hH.le) hp.le
      _ = _ := by ring
  have hbound : dist (F c) (F x) ≤ H / Real.sqrt Real.pi *
      diameterGauge (jacobianMeasure F) x y := by
    have hh := (div_le_iff₀ hH).1 (show
      Real.sqrt Real.pi * dist (F c) (F x) / H ≤
        diameterGauge (jacobianMeasure F) x y by simpa only [mul_div_assoc] using hblo)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hup : dist (F x) (F y) ≤ weakQSTwoScale H / Real.sqrt Real.pi *
      diameterGauge (jacobianMeasure F) x y := by
    calc
      _ ≤ (1 + H) * dist (F c) (F x) := hd
      _ ≤ (1 + H) * (H / Real.sqrt Real.pi * diameterGauge (jacobianMeasure F) x y) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
      _ = _ := by unfold weakQSTwoScale; ring
  constructor
  · apply (div_le_iff₀ hA).mpr
    calc
      _ ≤ (Real.sqrt Real.pi * H ^ 2) * dist (F x) (F y) := hlo
      _ ≤ dist (F x) (F y) * semmesGaugeConstant H := by
        unfold semmesGaugeConstant
        nlinarith [mul_nonneg (div_nonneg hT.le hp.le) (dist_nonneg (x := F x) (y := F y))]
  · exact hup.trans (mul_le_mul_of_nonneg_right
      (by unfold semmesGaugeConstant; linarith [mul_nonneg hp.le (sq_nonneg H)] : weakQSTwoScale H / Real.sqrt Real.pi ≤
        semmesGaugeConstant H) (diameterGauge_nonneg _ _ _))

/-- Main weak-QS Semmes producer, retaining the actual metric as a separate output. -/
theorem semmes_sameMap_metricDoubling :
    PositiveFiniteBalls (jacobianMeasure F) ∧
    GlobalDoublingWith (jacobianMeasure F) (semmesDoublingConstant H) ∧
    GaugeComparable (jacobianMeasure F) (pullbackMetric F) (semmesGaugeConstant H) :=
  ⟨jacobianMeasure_positiveFiniteBalls F hLocal hJ hQS,
    jacobianMeasure_globalDoubling F hLocal hJ hQS,
    jacobianMeasure_gaugeComparable F hLocal hJ hQS⟩

/-- Metric-doubling form of the same-map producer, with its witness constructed. -/
theorem jacobianMeasure_metricDoubling :
    MetricDoublingWith (jacobianMeasure F) (semmesDoublingConstant H) (semmesGaugeConstant H) :=
  ⟨jacobianMeasure_positiveFiniteBalls F hLocal hJ hQS,
    jacobianMeasure_globalDoubling F hLocal hJ hQS,
    pullbackMetric F, jacobianMeasure_gaugeComparable F hLocal hJ hQS⟩

/-- Bounded a.e. comparison C⁻¹ w ≤ J ≤ C w keeps this specific pullback metric. -/
theorem semmes_weight_sameMap_metricDoubling {w : ℂ → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (hcompare : ∀ᵐ z ∂volume,
      C⁻¹ * w z ≤ signedJacobian F z ∧ signedJacobian F z ≤ C * w z) :
    PositiveFiniteBalls (weightMeasure w) ∧
    GlobalDoublingWith (weightMeasure w) (C ^ 2 * semmesDoublingConstant H) ∧
    GaugeComparable (weightMeasure w) (pullbackMetric F)
      (Real.sqrt C * semmesGaugeConstant H) := by
  have hc := (weightMeasure_comparison_of_inverse hC hcompare).symm
  have hb := jacobianMeasure_positiveFiniteBalls F hLocal hJ hQS
  exact ⟨hb.transfer hc, (jacobianMeasure_globalDoubling F hLocal hJ hQS).transfer hc,
    (jacobianMeasure_gaugeComparable F hLocal hJ hQS).transfer hb hc⟩

/-- Existential metric-doubling packaging of the same-map comparable-weight output. -/
theorem semmes_weight_metricDoubling {w : ℂ → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (hcompare : ∀ᵐ z ∂volume,
      C⁻¹ * w z ≤ signedJacobian F z ∧ signedJacobian F z ≤ C * w z) :
    MetricDoublingWith (weightMeasure w) (C ^ 2 * semmesDoublingConstant H)
      (Real.sqrt C * semmesGaugeConstant H) := by
  obtain ⟨hb, hd, hg⟩ := semmes_weight_sameMap_metricDoubling F hLocal hJ hQS hC hcompare
  exact ⟨hb, hd, pullbackMetric F, hg⟩

/-- Explicit weak-QS constant produced by the proved analytic QC theorem. -/
def semmesQCConstant (K : ℝ) : ℝ :=
  (1 + Real.exp (9 * Real.pi ^ 2 * K / (4 * Real.log 2))) ^ 4 - 1

omit hJ hQS in
/-- Actual analytic QC assumptions produce all Semmes data, without assuming QS. -/
theorem semmes_sameMap_of_analytic_qc {K : ℝ} (hK : 0 ≤ K)
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x) :
    PositiveFiniteBalls (jacobianMeasure F) ∧
    GlobalDoublingWith (jacobianMeasure F) (semmesDoublingConstant (semmesQCConstant K)) ∧
    GaugeComparable (jacobianMeasure F) (pullbackMetric F)
      (semmesGaugeConstant (semmesQCConstant K)) :=
  semmes_sameMap_metricDoubling F hLocal (hQC.mono fun _ hx => hx.2.1)
    (weakQuasisymmetricWith_of_analytic_qc F hK hLocal hQC)

omit hJ hQS in
/-- The full weight-comparison wrapper has only actual analytic map hypotheses. -/
theorem semmes_weight_sameMap_of_analytic_qc {K C : ℝ} {w : ℂ → ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C)
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hcompare : ∀ᵐ z ∂volume,
      C⁻¹ * w z ≤ signedJacobian F z ∧ signedJacobian F z ≤ C * w z) :
    PositiveFiniteBalls (weightMeasure w) ∧
    GlobalDoublingWith (weightMeasure w) (C ^ 2 * semmesDoublingConstant (semmesQCConstant K)) ∧
    GaugeComparable (weightMeasure w) (pullbackMetric F)
      (Real.sqrt C * semmesGaugeConstant (semmesQCConstant K)) :=
  semmes_weight_sameMap_metricDoubling F hLocal (hQC.mono fun _ hx => hx.2.1)
    (weakQuasisymmetricWith_of_analytic_qc F hK hLocal hQC) hC hcompare

end RepulsiveCoulomb.PaperRoute
