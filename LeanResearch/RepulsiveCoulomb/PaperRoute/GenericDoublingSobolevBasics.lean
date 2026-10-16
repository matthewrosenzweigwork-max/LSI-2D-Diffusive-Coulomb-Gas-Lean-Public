import LeanResearch.RepulsiveCoulomb.PaperRoute.GlobalDoublingGrowth
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Measure foundations for the new global-doubling Sobolev route

Every measure below is arbitrary. Positive finite ambient balls supply local
finiteness and the mean limit by continuity. No point-product growth, sphere
nullity, endpoint inequality, or chosen local doubling witness is used.
-/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem PositiveFiniteBalls.locallyFinite {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun x => ?_⟩
  exact ⟨ball x 1, ball_mem_nhds x (by norm_num), (hμ x 1 (by norm_num)).2⟩

theorem PositiveFiniteBalls.ball_lt_top {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (c : ℂ) (r : ℝ) : μ (ball c r) < ⊤ := by
  by_cases hr : 0 < r
  · exact (hμ c r hr).2
  · simp [ball_eq_empty.mpr (le_of_not_gt hr)]

theorem PositiveFiniteBalls.continuous_ball_integrable {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {f : ℂ → ℝ} (hf : Continuous f)
    (c : ℂ) (r : ℝ) : IntegrableOn f (ball c r) μ := by
  let : IsLocallyFiniteMeasure μ := hμ.locallyFinite
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall

/-- Elementary finite-measure mean comparison, independent of all weight models. -/
theorem norm_setAverage_sub_const_le_generic {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤)
    {f : X → ℝ} (hf : IntegrableOn f S μ) (c : ℝ) :
    ‖(⨍ x in S, f x ∂μ) - c‖ ≤ ⨍ x in S, ‖f x - c‖ ∂μ := by
  have hc : IntegrableOn (fun _ : X => c) S μ := integrableOn_const hSfin
  have he : (⨍ x in S, f x - c ∂μ) = (⨍ x in S, f x ∂μ) - c := by
    rw [setAverage_fun_sub hf hc, setAverage_const hS0 hSfin]
  rw [← he]
  unfold average
  exact norm_integral_le_integral_norm _

theorem setAverage_nonneg_subset_bound_generic {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S T : Set X} (hST : S ⊆ T)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤) (hT0 : μ T ≠ 0) (hTfin : μ T ≠ ⊤)
    {g : X → ℝ} (hg : IntegrableOn g T μ) (hgn : ∀ x, 0 ≤ g x) :
    (⨍ x in S, g x ∂μ) ≤ (μ.real T / μ.real S) * ⨍ x in T, g x ∂μ := by
  have hm := setIntegral_mono_set hg (Eventually.of_forall hgn) (Eventually.of_forall hST)
  have hS : μ.real S ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hS0, hSfin⟩
  have hT : μ.real T ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hT0, hTfin⟩
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (μ.real S)⁻¹ * (∫ x in S, g x ∂μ) ≤
    (μ.real T / μ.real S) * ((μ.real T)⁻¹ * ∫ x in T, g x ∂μ)
  calc
    _ ≤ (μ.real S)⁻¹ * ∫ x in T, g x ∂μ :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = _ := by field_simp

theorem norm_nested_average_difference_le_generic {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S T : Set X} (hST : S ⊆ T)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤) (hT0 : μ T ≠ 0) (hTfin : μ T ≠ ⊤)
    {f : X → ℝ} (hf : IntegrableOn f T μ) :
    ‖(⨍ x in S, f x ∂μ) - (⨍ x in T, f x ∂μ)‖ ≤
      (μ.real T / μ.real S) * ⨍ x in T, ‖f x - (⨍ y in T, f y ∂μ)‖ ∂μ := by
  apply (norm_setAverage_sub_const_le_generic μ hS0 hSfin (hf.mono_set hST) _).trans
  exact setAverage_nonneg_subset_bound_generic μ hST hS0 hSfin hT0 hTfin
    (hf.sub (integrableOn_const hTfin)).norm (fun x => norm_nonneg _)

/-- Continuity, rather than a differentiation theorem or null-sphere assertion,
forces shrinking positive finite ball means to their center value. -/
theorem PositiveFiniteBalls.average_tendsto {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) :
    Tendsto (fun r : ℝ => ⨍ z in ball c r, f z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (f c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := c)) (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with r hr hrδ
  have hm := norm_setAverage_sub_const_le_generic μ (hμ c r hr).1.ne'
    (hμ c r hr).2.ne (hμ.continuous_ball_integrable hf c r) (f c)
  have hb : (⨍ z in ball c r, ‖f z - f c‖ ∂μ) ≤ ε / 2 := by
    have hi : IntegrableOn (fun z => ‖f z - f c‖) (ball c r) μ :=
      hμ.continuous_ball_integrable (hf.sub continuous_const).norm c r
    have hc : IntegrableOn (fun _ : ℂ => ε / 2) (ball c r) μ :=
      integrableOn_const (hμ c r hr).2.ne
    have hb' : (⨍ z in ball c r, ‖f z - f c‖ ∂μ) ≤ ⨍ _ in ball c r, ε / 2 ∂μ := by
      simp only [average_eq, smul_eq_mul]
      apply mul_le_mul_of_nonneg_left (integral_mono_ae hi hc ?_)
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      simpa only [dist_eq_norm] using (hclose ((mem_ball.mp hz).trans hrδ)).le
    simpa only [setAverage_const (hμ c r hr).1.ne' (hμ c r hr).2.ne] using hb'
  have hh : dist (⨍ z in ball c r, f z ∂μ) (f c) ≤ ε / 2 := by
    simpa only [dist_eq_norm] using hm.trans hb
  exact hh.trans_lt (by linarith)

/-- Radius of the mean telescoping balls; energy balls have five times this radius. -/
def doublingMeanRadius (R : ℝ) (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n * R

theorem doublingMeanRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < doublingMeanRadius R n := by unfold doublingMeanRadius; positivity

theorem doublingMeanRadius_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (doublingMeanRadius R) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (doublingMeanRadius_pos hR)⟩
  change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * R) atTop (𝓝 (0 : ℝ))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const R

theorem doublingMeanRadius_energy (R : ℝ) (n : ℕ) :
    5 * doublingMeanRadius (2 * R) n = doublingDyadicRadius R n := by
  unfold doublingMeanRadius doublingDyadicRadius
  ring

end RepulsiveCoulomb.PaperRoute
