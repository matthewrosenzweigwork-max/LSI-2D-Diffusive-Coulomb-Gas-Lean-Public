module

public import LeanResearch.RepulsiveCoulomb.PointHedbergBound
public import LeanResearch.RepulsiveCoulomb.HedbergPowerIdentity

@[expose] public section

/-! Quantitative pointwise Hedberg estimate for actual continuous observables,
conditional only on the displayed weak (1,2) Poincare estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointHedbergConstant (Q P : ℝ) : ℝ :=
  10 * P * (rawPointDoublingConstant Q + rawPointInitialMeanConstant Q)

theorem pointHedbergConstant_pos (Q : ℝ) {P : ℝ} (hP : 0 < P) :
    0 < pointHedbergConstant Q P := by
  unfold pointHedbergConstant
  exact mul_pos (mul_pos (by norm_num) hP)
    (add_pos (rawPointDoublingConstant_pos Q) (rawPointInitialMeanConstant_pos Q))

theorem pointPoincareSeries_power_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z) :
    pointPoincareSeries a y R g x ≤ ENNReal.ofReal
      (5 * (pointLocalMaximalEnergy a y c R g x).toReal ^ pointSobolevMaximalExponent Q *
        (pointLocalEnergy Q a y c R g) ^ pointSobolevGain Q) := by
  have h := pointPoincareSeries_hedberg ha hQ y hR hx g hg hgn
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have he := hedberg_sqrt_quotient_eq_power (M := (pointLocalMaximalEnergy a y c R g x).toReal)
    hQ0 ENNReal.toReal_nonneg
    (pointLocalEnergy_nonneg Q a y c R g hgn)
  have he5 := congrArg (fun t : ℝ => 5 * t) he
  simp only [← mul_div_assoc, ← mul_assoc] at he5
  rw [he5] at h
  exact h

theorem rawPointMeasure_hedberg_oscillation {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂rawPointMeasure a y))
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ≤
      pointHedbergConstant Q P * R *
        (pointLocalMaximalEnergy a y c R g x).toReal ^ pointSobolevMaximalExponent Q *
        (pointLocalEnergy Q a y c R g) ^ pointSobolevGain Q := by
  have h := (rawPointMeasure_oscillation_le_series ha hQ hP.le y f g hf hPI c hR hx).trans
    (mul_le_mul' le_rfl (pointPoincareSeries_power_bound ha hQ y hR hx g hg hgn))
  have hC : 0 ≤ 2 * R * P * (rawPointDoublingConstant Q + rawPointInitialMeanConstant Q) := by
    have := (rawPointDoublingConstant_pos Q).le
    have := (rawPointInitialMeanConstant_pos Q).le
    positivity
  rw [← ENNReal.ofReal_mul hC] at h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal (by
    apply mul_nonneg hC
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg (pointLocalEnergy_nonneg Q a y c R g hgn) _))] at ht
  convert ht using 1
  unfold pointHedbergConstant
  ring

end RepulsiveCoulomb
