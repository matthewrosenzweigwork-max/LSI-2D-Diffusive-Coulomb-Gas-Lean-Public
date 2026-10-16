module

public import LeanResearch.RepulsiveCoulomb.RawPointVolumeGrowth

@[expose] public section

/-! Actual weighted ball averages of continuous observables converge at every
point, including positive punctures. No differentiation theorem or Poincare
hypothesis is needed for this step of the dyadic argument. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def rawPointBallAverage {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  (∫ z in closedBall c r, f z * rawPointWeight a y z) /
    (∫ z in closedBall c r, rawPointWeight a y z)

theorem rawPointBallIntegral_pos {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < ∫ z in closedBall c r, rawPointWeight a y z := by
  have h := rawPointMeasure_ball_pos ha y c hr
  rw [← rawPointMeasure_closedBall_eq_ball a y c r, rawPointMeasure_closedBall ha y c r] at h
  exact ENNReal.ofReal_pos.mp h

theorem rawPointBallAverage_oscillation_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (f : ℂ → ℝ) (hf : Continuous f)
    (c : ℂ) {r : ℝ} (hr : 0 < r) {ε : ℝ}
    (hb : ∀ z ∈ closedBall c r, |f z - f c| ≤ ε) :
    |rawPointBallAverage a y f c r - f c| ≤ ε := by
  let M := ∫ z in closedBall c r, rawPointWeight a y z
  have hM : 0 < M := rawPointBallIntegral_pos ha y c hr
  have hw := rawPointWeight_continuous ha y
  have hI : IntegrableOn (fun z => f z * rawPointWeight a y z) (closedBall c r) :=
    (hf.mul hw).continuousOn.integrableOn_compact (isCompact_closedBall c r)
  have hJ : IntegrableOn (fun z => (f z - f c) * rawPointWeight a y z) (closedBall c r) :=
    ((hf.sub continuous_const).mul hw).continuousOn.integrableOn_compact (isCompact_closedBall c r)
  have he : rawPointBallAverage a y f c r - f c =
      (∫ z in closedBall c r, (f z - f c) * rawPointWeight a y z) / M := by
    unfold rawPointBallAverage
    simp_rw [sub_mul]
    rw [integral_sub hI ((rawPointWeight_ball_integrable ha y c r).const_mul (f c)), integral_const_mul]
    change _ / M - f c = (_ - f c * M) / M
    field_simp [hM.ne']
    <;> ring
  rw [he, abs_div, abs_of_pos hM]
  apply (div_le_iff₀ hM).mpr
  have hnorm : |∫ z in closedBall c r, (f z - f c) * rawPointWeight a y z| ≤
      ∫ z in closedBall c r, |(f z - f c) * rawPointWeight a y z| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict (closedBall c r)) (fun z => (f z - f c) * rawPointWeight a y z)
  apply hnorm.trans
  change (∫ z in closedBall c r, |(f z - f c) * rawPointWeight a y z|) ≤ ε * M
  rw [show ε * M = ∫ z in closedBall c r, ε * rawPointWeight a y z by rw [integral_const_mul]]
  apply integral_mono_ae hJ.norm ((rawPointWeight_ball_integrable ha y c r).const_mul ε)
  filter_upwards [self_mem_ae_restrict measurableSet_closedBall] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rawPointWeight_nonneg a y z)]
  exact mul_le_mul_of_nonneg_right (hb z hz) (rawPointWeight_nonneg a y z)

theorem rawPointBallAverage_tendsto {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) :
    Tendsto (rawPointBallAverage a y f c) (𝓝[>] (0 : ℝ)) (𝓝 (f c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with r hr hrδ
  have hbound := rawPointBallAverage_oscillation_le ha y f hf c hr (ε := ε / 2) (by
    intro z hz
    have hzδ : dist z c < δ := (mem_closedBall.mp hz).trans_lt hrδ
    simpa only [Real.dist_eq] using (hclose hzδ).le)
  rw [Real.dist_eq]
  exact hbound.trans_lt (by linarith)

end RepulsiveCoulomb
