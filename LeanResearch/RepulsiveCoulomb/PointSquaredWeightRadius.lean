module

public import LeanResearch.RepulsiveCoulomb.PointGlobalMeanOscillation
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-! The raw/squared-weight Cauchy--Schwarz radius factor in Bjorn's p=1
transfer. Applying strong A-infinity to the doubled exponents yields the exact
squared weight; no new configuration restrictions are imposed. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointWeight_double_exponents {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) :
    rawPointWeight (fun j => 2 * a j) y z = rawPointWeight a y z ^ 2 := by
  unfold rawPointWeight
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  change ‖z - y j‖ ^ (2 * a j) = (‖z - y j‖ ^ a j) ^ 2
  rw [show 2 * a j = a j * (2 : ℝ) by ring, Real.rpow_mul (norm_nonneg _), Real.rpow_two]

theorem rawPointMeasure_ball_real_eq_integral {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) (r : ℝ) :
    (rawPointMeasure a y).real (ball c r) = ∫ z in closedBall c r, rawPointWeight a y z := by
  unfold Measure.real
  rw [← rawPointMeasure_closedBall_eq_ball a y c r, rawPointMeasure_closedBall ha y c r,
    ENNReal.toReal_ofReal (integral_nonneg (rawPointWeight_nonneg a y))]

theorem rawPointMeasure_cauchy_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (rawPointMeasure a y).real (ball c r) ≤ Real.sqrt Real.pi * r *
      Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r)) := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  rw [rawPointMeasure_ball_real_eq_integral ha y c r,
    rawPointMeasure_ball_real_eq_integral ha2 y c r]
  simp_rw [rawPointWeight_double_exponents]
  let μ : Measure ℂ := volume.restrict (closedBall c r)
  let V := Real.pi * r ^ 2
  let I := ∫ z, rawPointWeight a y z ∂μ
  let J := ∫ z, rawPointWeight a y z ^ 2 ∂μ
  have hV : 0 < V := by dsimp [V]; positivity
  have hv : μ.real univ = V := by
    simp [μ, V, Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le, mul_comm]
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using (isCompact_closedBall c r).measure_lt_top⟩
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun ν : Measure ℂ => ν.real univ) h
    rw [hv] at he
    have : V = 0 := by simpa [Measure.real] using he
    linarith⟩
  have hi : Integrable (rawPointWeight a y) μ := rawPointWeight_ball_integrable ha y c r
  have hj : Integrable (fun z => rawPointWeight a y z ^ 2) μ :=
    ((rawPointWeight_continuous ha y).pow 2).continuousOn.integrableOn_compact (isCompact_closedBall c r)
  have hm := (convexOn_pow (𝕜 := ℝ) 2).map_average_le (μ := μ)
    (continuous_pow 2).continuousOn isClosed_Ici
    (Eventually.of_forall (fun z => rawPointWeight_nonneg a y z)) hi hj
  simp only [average_eq, smul_eq_mul, hv] at hm
  change (V⁻¹ * I) ^ 2 ≤ V⁻¹ * J at hm
  have hs : I ^ 2 ≤ V * J := by
    calc
      _ = V ^ 2 * (V⁻¹ * I) ^ 2 := by field_simp
      _ ≤ V ^ 2 * (V⁻¹ * J) := mul_le_mul_of_nonneg_left hm (sq_nonneg V)
      _ = _ := by field_simp
  have h := Real.le_sqrt_of_sq_le hs
  rw [Real.sqrt_mul hV.le] at h
  have hsV : Real.sqrt V = Real.sqrt Real.pi * r := by
    change Real.sqrt (Real.pi * r ^ 2) = _
    rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hr.le]
  rw [hsV] at h
  exact h

theorem rawPointMeasure_squared_weight_radius_factor {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (rawPointMeasure a y).real (ball c (2 * r)) /
      Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r)) ≤
        rawPointDoublingConstant Q * Real.sqrt Real.pi * r := by
  have ha2 : ∀ j, 0 ≤ 2 * a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hpos : 0 < Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r)) :=
    Real.sqrt_pos.mpr (ENNReal.toReal_pos (rawPointMeasure_ball_pos ha2 y c hr).ne'
      (rawPointMeasure_ball_lt_top ha2 y c r).ne)
  apply (div_le_iff₀ hpos).mpr
  exact (rawPointMeasure_doubling_real ha hQ y c hr).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (rawPointMeasure_cauchy_radius ha y c hr) (rawPointDoublingConstant_pos Q).le))

end RepulsiveCoulomb
