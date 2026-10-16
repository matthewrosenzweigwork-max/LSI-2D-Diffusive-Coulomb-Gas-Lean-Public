module

public import LeanResearch.RepulsiveCoulomb.PointDoubleOscillationReal

@[expose] public section

/-! The actual configuration-uniform David--Semmes double-average estimate for
the literal point weights, every C1 observable, every positive radius and exact
physical gradient. No analytic estimate or approximation remains a hypothesis. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def pointDavidSemmesConstant (Q : ℝ) : ℝ := 2 * Real.sqrt (pointGridRelativeIsoperimetricConstant Q)

theorem pointDavidSemmesConstant_pos (Q : ℝ) : 0 < pointDavidSemmesConstant Q :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr (pointGridRelativeIsoperimetricConstant_pos Q))

theorem double_oscillation_normalize {D E M C : ℝ} (hM : 0 < M)
    (h : D ≤ (2 * (M * Real.sqrt (M*C))) * E) :
    D / M^2 ≤ (2 * Real.sqrt C / Real.sqrt M) * E := by
  calc
    _ ≤ ((2 * (M * Real.sqrt (M*C))) * E) / M^2 :=
      div_le_div_of_nonneg_right h (sq_nonneg M)
    _ = 2 * (Real.sqrt M / M) * Real.sqrt C * E := by
      rw [Real.sqrt_mul hM.le]
      field_simp [hM.ne']
      <;> ring
    _ = _ := by rw [Real.sqrt_div_self']; ring

theorem rawPoint_DavidSemmes_estimate {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (x : ℂ) {R : ℝ} (hR : 0 < R) :
    rawPointDoubleAverageOscillation (fun j => 2*a j) y f x R ≤
      pointDavidSemmesConstant Q * ((rawPointMeasure a y).real (ball x (2*R)) /
        Real.sqrt ((rawPointMeasure (fun j => 2*a j) y).real (ball x R))) *
        ⨍ z in ball x (2*R), ‖gradient f z‖ ∂rawPointMeasure a y := by
  let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
  let E := ∫ z in ball x (2*R), ‖gradient f z‖ * rawPointWeight a y z
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hM : 0 < M := ENNReal.toReal_pos (rawPointMeasure_ball_pos ha2 y x hR).ne'
    (rawPointMeasure_ball_lt_top ha2 y x R).ne
  have hreal := rawPoint_C1_double_oscillation_real ha hQ y hf x hR
  have hnorm := double_oscillation_normalize hM hreal
  have hE : E = (rawPointMeasure a y).real (ball x (2*R)) *
      ⨍ z in ball x (2*R), ‖gradient f z‖ ∂rawPointMeasure a y := by
    change (∫ z in ball x (2*R), ‖gradient f z‖ * rawPointWeight a y z) = _
    rw [← rawPointMeasure_setIntegral ha y (fun z => ‖gradient f z‖) isOpen_ball.measurableSet]
    simpa only [smul_eq_mul] using (measure_smul_setAverage (μ := rawPointMeasure a y)
      (fun z => ‖gradient f z‖) (rawPointMeasure_ball_lt_top ha y x (2*R)).ne).symm
  rw [rawPointDoubleAverageOscillation_eq_product ha2 y hf.continuous x R]
  calc
    _ ≤ (2 * Real.sqrt (pointGridRelativeIsoperimetricConstant Q) / Real.sqrt M) * E := hnorm
    _ = _ := by rw [hE]; unfold pointDavidSemmesConstant; ring

end RepulsiveCoulomb
