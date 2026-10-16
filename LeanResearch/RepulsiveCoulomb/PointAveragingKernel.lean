module

public import LeanResearch.RepulsiveCoulomb.PointBallMassComparison

@[expose] public section

/-! The moving-ball averaging kernel has uniformly bounded mass in its center
variable. This is the actual doubling-measure kernel estimate needed in Bjorn's
Fubini step, with constants fixed before the point configuration. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointAveragingKernel {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (r : ℝ) (x z : ℂ) : ℝ :=
  if dist z x < r then ((rawPointMeasure a y).real (ball x r))⁻¹ else 0

theorem rawPointAveragingKernel_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (r : ℝ) (x z : ℂ) : 0 ≤ rawPointAveragingKernel a y r x z := by
  unfold rawPointAveragingKernel
  split_ifs <;> positivity

theorem measurable_rawPointAveragingKernel {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (r : ℝ) :
    Measurable (fun p : ℂ × ℂ => rawPointAveragingKernel a y r p.1 p.2) := by
  have hm : Measurable (fun x : ℂ => ((rawPointMeasure a y).real (ball x r))⁻¹) :=
    (measurable_rawPointMeasure_ball ha y r).ennreal_toReal.inv
  exact (hm.comp measurable_fst).ite
    (measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const) measurable_const

theorem rawPointAveragingKernel_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {r : ℝ} (hr : 0 < r) (x z : ℂ) :
    rawPointAveragingKernel a y r x z ≤
      (ball z r).indicator (fun _ => rawPointDoublingConstant Q /
        (rawPointMeasure a y).real (ball z r)) x := by
  by_cases hzx : dist z x < r
  · have hx : x ∈ ball z r := by simpa only [mem_ball, dist_comm] using hzx
    rw [Set.indicator_of_mem hx, rawPointAveragingKernel, if_pos hzx]
    have hxpos : 0 < (rawPointMeasure a y).real (ball x r) :=
      ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y x hr).ne' (rawPointMeasure_ball_lt_top ha y x r).ne
    have hzpos : 0 < (rawPointMeasure a y).real (ball z r) :=
      ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y z hr).ne' (rawPointMeasure_ball_lt_top ha y z r).ne
    apply (le_div_iff₀ hzpos).mpr
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hxpos).mpr (rawPointMeasure_neighbor_ball_real ha hQ y hr hzx)
  · have hx : x ∉ ball z r := by simpa only [mem_ball, dist_comm] using hzx
    rw [Set.indicator_of_notMem hx, rawPointAveragingKernel, if_neg hzx]

theorem rawPointAveragingKernel_integrable {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (fun x => rawPointAveragingKernel a y r x z) (rawPointMeasure a y) := by
  have hI : Integrable ((ball z r).indicator (fun _ : ℂ => rawPointDoublingConstant Q /
      (rawPointMeasure a y).real (ball z r))) (rawPointMeasure a y) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (rawPointMeasure_ball_lt_top ha y z r).ne)
  have hm : Measurable (fun x => rawPointAveragingKernel a y r x z) := by
    simpa only [Function.comp_def, id_eq] using (measurable_rawPointAveragingKernel ha y r).comp
      (measurable_id.prodMk (measurable_const (a := z)))
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (rawPointAveragingKernel_nonneg a y r x z)]
  exact rawPointAveragingKernel_bound ha hQ y hr x z

theorem rawPointAveragingKernel_integral_le {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫ x, rawPointAveragingKernel a y r x z ∂rawPointMeasure a y) ≤ rawPointDoublingConstant Q := by
  have hI : Integrable ((ball z r).indicator (fun _ : ℂ => rawPointDoublingConstant Q /
      (rawPointMeasure a y).real (ball z r))) (rawPointMeasure a y) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (rawPointMeasure_ball_lt_top ha y z r).ne)
  have h := integral_mono (rawPointAveragingKernel_integrable ha hQ y hr z) hI
    (fun x => rawPointAveragingKernel_bound ha hQ y hr x z)
  rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul] at h
  have hzpos : 0 < (rawPointMeasure a y).real (ball z r) :=
    ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y z hr).ne' (rawPointMeasure_ball_lt_top ha y z r).ne
  have he : (rawPointMeasure a y).real (ball z r) *
      (rawPointDoublingConstant Q / (rawPointMeasure a y).real (ball z r)) = rawPointDoublingConstant Q := by
    field_simp [hzpos.ne']
  rwa [he] at h

end RepulsiveCoulomb
