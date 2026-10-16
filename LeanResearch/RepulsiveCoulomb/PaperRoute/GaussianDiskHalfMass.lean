import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianLocalGeometry
import LeanResearch.RepulsiveCoulomb.UnitDiskUniformTails
import Mathlib.MeasureTheory.Measure.TightNormed

/-! Additive experimental source. Verification status is recorded separately in evidence. The actual half-mass disk is obtained
from the manuscript's literal unit-disk logarithmic-average/Jensen partition
lower bound. The older annular normalization witness is not selected. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb.PaperRoute

def diskEnvelopeMeasure (γ Q : ℝ) : Measure ℂ :=
  (ENNReal.ofReal (pointDiskLowerConstant γ Q))⁻¹ •
    volume.withDensity (fun z ↦ ENNReal.ofReal (pointEnvelope γ Q z))

theorem diskEnvelopeMeasure_finite {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    IsFiniteMeasure (diskEnvelopeMeasure γ Q) := by
  constructor
  simp only [diskEnvelopeMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (pointDiskLowerConstant_pos γ Q))
  · exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (pointEnvelope_nonneg γ Q))).mp (pointEnvelope_integrable hγ hQ).hasFiniteIntegral

theorem pointMeasure_le_diskEnvelopeMeasure {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    pointMeasure γ a y s ≤ diskEnvelopeMeasure γ Q s := by
  simpa only [diskEnvelopeMeasure, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
    using pointMeasure_le_disk_envelope hγ ha hQ y hs


theorem diskEnvelopeMeasure_tail_tendsto {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    Tendsto (fun R : ℝ ↦ diskEnvelopeMeasure γ Q {z | R < ‖z‖}) atTop (𝓝 0) := by
  let : IsFiniteMeasure (diskEnvelopeMeasure γ Q) := diskEnvelopeMeasure_finite hγ hQ
  have h := tendsto_measure_norm_gt_of_isTightMeasureSet
    (isTightMeasureSet_singleton (μ := diskEnvelopeMeasure γ Q))
  simpa using h

/-- The radius is chosen before the entire finite point family. -/
theorem disk_half_mass_ball {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ R : ℝ, 1 ≤ R ∧ UniformHalfMassBall γ Q R := by
  obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp
    (diskEnvelopeMeasure_tail_tendsto hγ hQ) (1 / 2) (by norm_num)
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
    (pointMeasure_le_diskEnvelopeMeasure hγ ha hsum y Metric.isOpen_ball.measurableSet.compl).trans
      ((measure_mono hsub).trans (hR R le_rfl))
  calc
    (1 / 2 : ENNReal) = 1 - 1 / 2 := by norm_num
    _ ≤ 1 - pointMeasure γ a y (Metric.ball (0 : ℂ) (max 1 (R + 1)))ᶜ :=
      tsub_le_tsub_left htail 1
    _ = pointMeasure γ a y (Metric.ball (0 : ℂ) (max 1 (R + 1))) := by
      simpa only [measure_univ, compl_compl] using
        (measure_compl Metric.isOpen_ball.measurableSet.compl
          (measure_ne_top (pointMeasure γ a y) (Metric.ball (0 : ℂ) (max 1 (R + 1)))ᶜ)).symm

end RepulsiveCoulomb.PaperRoute
