import LeanResearch.RepulsiveCoulomb.PointCompactC1DoubleOscillation
import LeanResearch.RepulsiveCoulomb.LocalCompactObservable

/-! Actual double oscillation for every C1 observable, localized to the exact
observation and doubled balls. No compact-support hypothesis remains. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem rawPoint_C1_double_oscillation {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℂ) {R : ℝ} (hR : 0 < R) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
    let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
    (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1 - f q.2| ∂ν.prod ν) ≤
      2 * ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)) *
        ∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient f z‖ * ENNReal.ofReal (rawPointWeight a y z) := by
  obtain ⟨g,hgC,hgcompact,hg⟩ := exists_compact_c1_agree_on_closedBall hf x (by positivity : 0 < 2*R)
  let μ := rawPointMeasure (fun j => 2*a j) y
  let ν := μ.restrict (ball x R)
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  letI := rawPointMeasure_locallyFinite ha2 y
  have hleft : (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |g q.1-g q.2| ∂ν.prod ν) =
      ∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1-f q.2| ∂ν.prod ν := by
    change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |g q.1-g q.2| ∂(μ.restrict (ball x R)).prod (μ.restrict (ball x R))) = _
    rw [Measure.prod_restrict]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet.prod isOpen_ball.measurableSet)] with q hq
    have hq1 : q.1 ∈ closedBall x (2*R) :=
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hq.1)
    have hq2 : q.2 ∈ closedBall x (2*R) :=
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hq.2)
    rw [(hg q.1 hq1).eq_of_nhds,(hg q.2 hq2).eq_of_nhds]
  have hright : (∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient g z‖ * ENNReal.ofReal (rawPointWeight a y z)) =
      ∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient f z‖ * ENNReal.ofReal (rawPointWeight a y z) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    rw [gradient_eq_of_eventuallyEq (hg z (ball_subset_closedBall hz))]
  have hb := rawPoint_compactC1_double_oscillation ha hQ y hgC hgcompact x hR
  change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |g q.1-g q.2| ∂ν.prod ν) ≤ _ at hb
  rw [hleft,hright] at hb
  exact hb

end RepulsiveCoulomb
