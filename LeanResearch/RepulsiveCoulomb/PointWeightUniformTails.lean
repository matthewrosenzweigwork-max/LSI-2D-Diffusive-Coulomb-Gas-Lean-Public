import LeanResearch.RepulsiveCoulomb.PointWeightAnnularNormalization
import Mathlib.MeasureTheory.Measure.TightNormed

/-! Configuration-uniform domination and tails of the normalized point weight.
The location factor is cancelled only after its strict positivity and finiteness
have been proved. The dominating measure depends on the Gaussian parameter and
total-exponent bound alone. It is not a weighted Sobolev compactness assertion.
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb

theorem pointWeight_integral_lower_uniform {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    pointLowerConstant γ Q * pointLocationFactor a y ≤ ∫ z : ℂ, pointWeight γ a y z := by
  have h := pointPartition_lower_uniform hγ ha hQ y
  rw [pointPartition_eq_ofReal_integral hγ ha y] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (pointWeight_nonneg γ a y))).mp h

theorem pointMeasure_le_envelope {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    pointMeasure γ a y s ≤ (ENNReal.ofReal (pointLowerConstant γ Q))⁻¹ *
      ∫⁻ z in s, ENNReal.ofReal (pointEnvelope γ Q z) := by
  have hA0 : ENNReal.ofReal (pointLocationFactor a y) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pointLocationFactor_pos a y))
  have hC0 : ENNReal.ofReal (pointLowerConstant γ Q) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pointLowerConstant_pos γ Q))
  have hP := pointPartition_lower_uniform hγ ha hQ y
  rw [ENNReal.ofReal_mul (pointLowerConstant_pos γ Q).le] at hP
  have hratio : (pointPartition γ a y)⁻¹ * ENNReal.ofReal (pointLocationFactor a y) ≤
      (ENNReal.ofReal (pointLowerConstant γ Q))⁻¹ := by
    calc
      _ ≤ (ENNReal.ofReal (pointLowerConstant γ Q) *
          ENNReal.ofReal (pointLocationFactor a y))⁻¹ * ENNReal.ofReal (pointLocationFactor a y) :=
        mul_le_mul_left (ENNReal.inv_le_inv.mpr hP) _
      _ = _ := by
        rw [ENNReal.mul_inv (Or.inl hC0) (Or.inl ENNReal.ofReal_ne_top),
          ENNReal.inv_mul_cancel_right hA0 ENNReal.ofReal_ne_top]
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ ↦ ha j)).trans hQ
  rw [pointMeasure, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  calc
    _ ≤ (pointPartition γ a y)⁻¹ *
        ∫⁻ z in s, ENNReal.ofReal (pointLocationFactor a y * pointEnvelope γ Q z) := by
      gcongr with z
      exact pointWeight_le_envelope γ ha hQ y z
    _ = ((pointPartition γ a y)⁻¹ * ENNReal.ofReal (pointLocationFactor a y)) *
        ∫⁻ z in s, ENNReal.ofReal (pointEnvelope γ Q z) := by
      simp_rw [ENNReal.ofReal_mul (pointLocationFactor_pos a y).le]
      rw [lintegral_const_mul _ (pointEnvelope_continuous γ hQ0).measurable.ennreal_ofReal,
        ← mul_assoc]
    _ ≤ _ := mul_le_mul_left hratio _

def pointEnvelopeMeasure (γ Q : ℝ) : Measure ℂ :=
  (ENNReal.ofReal (pointLowerConstant γ Q))⁻¹ •
    volume.withDensity (fun z ↦ ENNReal.ofReal (pointEnvelope γ Q z))

theorem pointEnvelopeMeasure_finite {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    IsFiniteMeasure (pointEnvelopeMeasure γ Q) := by
  constructor
  simp only [pointEnvelopeMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (pointLowerConstant_pos γ Q))
  · exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (pointEnvelope_nonneg γ Q))).mp (pointEnvelope_integrable hγ hQ).hasFiniteIntegral

theorem pointMeasure_le_envelopeMeasure {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    pointMeasure γ a y s ≤ pointEnvelopeMeasure γ Q s := by
  simpa only [pointEnvelopeMeasure, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
    using pointMeasure_le_envelope hγ ha hQ y hs


theorem pointMeasure_tail_le {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (R : ℝ) :
    pointMeasure γ a y {z | R < ‖z‖} ≤
      ENNReal.ofReal ((pointLowerConstant γ Q)⁻¹ *
        ∫ z : ℂ in {z | R < ‖z‖}, pointEnvelope γ Q z) := by
  have hQ0 := (Finset.sum_nonneg (fun j _ ↦ ha j)).trans hQ
  have hs : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const continuous_norm.measurable
  have h := pointMeasure_le_envelope hγ ha hQ y hs
  rw [← ofReal_integral_eq_lintegral_ofReal (pointEnvelope_integrable hγ hQ0).restrict
    (Eventually.of_forall (pointEnvelope_nonneg γ Q)),
    ← ENNReal.ofReal_inv_of_pos (pointLowerConstant_pos γ Q),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pointLowerConstant_pos γ Q).le)] at h
  exact h

theorem pointMeasure_tail_real_le {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (R : ℝ) :
    (pointMeasure γ a y).real {z | R < ‖z‖} ≤
      (pointLowerConstant γ Q)⁻¹ * ∫ z : ℂ in {z | R < ‖z‖}, pointEnvelope γ Q z := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (pointMeasure_tail_le hγ ha hQ y R)
  simpa only [Measure.real, ENNReal.toReal_ofReal
    (mul_nonneg (inv_nonneg.mpr (pointLowerConstant_pos γ Q).le)
      (integral_nonneg (pointEnvelope_nonneg γ Q)))] using h

theorem pointEnvelopeMeasure_tail_tendsto {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    Tendsto (fun R : ℝ ↦ pointEnvelopeMeasure γ Q {z | R < ‖z‖}) atTop (𝓝 0) := by
  let : IsFiniteMeasure (pointEnvelopeMeasure γ Q) := pointEnvelopeMeasure_finite hγ hQ
  have h := tendsto_measure_norm_gt_of_isTightMeasureSet
    (isTightMeasureSet_singleton (μ := pointEnvelopeMeasure γ Q))
  simpa using h

/-- The radius is chosen before the entire finite point family. -/
theorem pointMeasure_half_mass_ball {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (y : Fin m → ℂ),
      (∀ j, 0 ≤ a j) → (∑ j, a j ≤ Q) →
      (1 / 2 : ENNReal) ≤ pointMeasure γ a y (Metric.ball (0 : ℂ) R) := by
  obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp
    (pointEnvelopeMeasure_tail_tendsto hγ hQ) (1 / 2) (by norm_num)
  refine ⟨max 1 (R + 1), le_max_left _ _, ?_⟩
  intro m a y ha hsum
  let : IsProbabilityMeasure (pointMeasure γ a y) := pointMeasure_isProbability hγ ha y
  have hsub : (Metric.ball (0 : ℂ) (max 1 (R + 1)))ᶜ ⊆ {z : ℂ | R < ‖z‖} := by
    intro z hz
    have hn : max 1 (R + 1) ≤ ‖z‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hmax := le_max_right (1 : ℝ) (R + 1)
    change R < ‖z‖
    linarith
  have htail : pointMeasure γ a y (Metric.ball (0 : ℂ) (max 1 (R + 1)))ᶜ ≤ 1 / 2 :=
    (pointMeasure_le_envelopeMeasure hγ ha hsum y Metric.isOpen_ball.measurableSet.compl).trans
      ((measure_mono hsub).trans (hR R le_rfl))
  calc
    (1 / 2 : ENNReal) = 1 - 1 / 2 := by norm_num
    _ ≤ 1 - pointMeasure γ a y (Metric.ball (0 : ℂ) (max 1 (R + 1)))ᶜ :=
      tsub_le_tsub_left htail 1
    _ = pointMeasure γ a y (Metric.ball (0 : ℂ) (max 1 (R + 1))) := by
      simpa only [measure_univ, compl_compl] using
        (measure_compl Metric.isOpen_ball.measurableSet.compl
          (measure_ne_top (pointMeasure γ a y) (Metric.ball (0 : ℂ) (max 1 (R + 1)))ᶜ)).symm

/-- The complete normalization-and-tail conclusion of manuscript Lemma 3.3,
with one pair of constants and one radius chosen before all configurations.
The annular proof supplies an admissible constant, not the sharper disk value. -/
theorem uniform_pointWeight_normalization_and_tails {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ c C R : ℝ, 0 < c ∧ c ≤ C ∧ 1 ≤ R ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (y : Fin m → ℂ),
        (∀ j, 0 ≤ a j) → (∑ j, a j ≤ Q) →
        c * pointLocationFactor a y ≤ (∫ z : ℂ, pointWeight γ a y z) ∧
        (∫ z : ℂ, pointWeight γ a y z) ≤ C * pointLocationFactor a y ∧
        (∀ T : ℝ, (pointMeasure γ a y).real {z | T < ‖z‖} ≤
          C * ∫ z : ℂ in {z | T < ‖z‖}, pointEnvelope γ Q z) ∧
        (1 / 2 : ENNReal) ≤ pointMeasure γ a y (Metric.ball (0 : ℂ) R) := by
  let c := pointLowerConstant γ Q
  let C := max c (max (∫ z : ℂ, pointEnvelope γ Q z) c⁻¹)
  obtain ⟨R, hR, hmass⟩ := pointMeasure_half_mass_ball hγ hQ
  refine ⟨c, C, R, pointLowerConstant_pos γ Q, le_max_left _ _, hR, ?_⟩
  intro m a y ha hsum
  have hI : (∫ z : ℂ, pointEnvelope γ Q z) ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcinv : c⁻¹ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨pointWeight_integral_lower_uniform hγ ha hsum y, ?_, ?_, hmass m a y ha hsum⟩
  · calc
      (∫ z : ℂ, pointWeight γ a y z) ≤
          ∫ z : ℂ, pointLocationFactor a y * pointEnvelope γ Q z :=
        integral_mono (pointWeight_integrable hγ ha y)
          ((pointEnvelope_integrable hγ hQ).const_mul _) (pointWeight_le_envelope γ ha hsum y)
      _ = pointLocationFactor a y * ∫ z : ℂ, pointEnvelope γ Q z := integral_const_mul _ _
      _ ≤ pointLocationFactor a y * C :=
        mul_le_mul_of_nonneg_left hI (pointLocationFactor_pos a y).le
      _ = C * pointLocationFactor a y := mul_comm _ _
  · intro T
    exact (pointMeasure_tail_real_le hγ ha hsum y T).trans
      (mul_le_mul_of_nonneg_right hcinv (integral_nonneg (pointEnvelope_nonneg γ Q)))

end RepulsiveCoulomb
