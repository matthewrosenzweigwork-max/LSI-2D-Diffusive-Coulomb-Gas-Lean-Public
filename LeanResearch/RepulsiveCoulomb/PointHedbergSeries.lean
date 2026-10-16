module

public import LeanResearch.RepulsiveCoulomb.PointLocalEnergyScale
public import LeanResearch.RepulsiveCoulomb.DyadicHedberg

@[expose] public section

/-! The actual local square-root energy series and its optimized bound.
Positive and zero energy/maximal cases are all treated explicitly. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointPoincareSeries {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (R : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
    Real.sqrt (⨍ z in ball x (5 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y))

theorem pointPoincareSeries_hedberg_pos {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hE : 0 < pointLocalEnergy Q a y c R g)
    (hM : 0 < (pointLocalMaximalEnergy a y c R g x).toReal) :
    pointPoincareSeries a y R g x ≤ ENNReal.ofReal
      (5 * Real.sqrt (pointLocalMaximalEnergy a y c R g x).toReal /
        (Real.sqrt (pointLocalMaximalEnergy a y c R g x).toReal /
          Real.sqrt (pointLocalEnergy Q a y c R g)) ^ (1 / (Q + 2))) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  apply dyadic_series_hedberg (Real.sqrt_pos.mpr hM) (Real.sqrt_pos.mpr hE) (by linarith)
  · intro n
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (pointLocalMaximalEnergy_sqrt_average_bound ha y hR hx g hg hgn n)
      (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity)
  · intro n
    convert ENNReal.ofReal_le_ofReal (pointLocalEnergy_scaled_average_bound ha hQ y hR hx g hg hgn n) using 1 <;>
      congr 1 <;> ring

theorem pointPoincareSeries_zero_of_energy_zero {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hE : pointLocalEnergy Q a y c R g = 0) : pointPoincareSeries a y R g x = 0 := by
  apply dyadic_series_zero_of_zero_bound
  intro n
  have h := ENNReal.ofReal_le_ofReal (pointLocalEnergy_scaled_average_bound ha hQ y hR hx g hg hgn n)
  simpa only [hE, Real.sqrt_zero, zero_mul, ENNReal.ofReal_zero] using h

theorem pointPoincareSeries_zero_of_maximal_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c x : ℂ} {R : ℝ} (hR : 0 < R) (hx : x ∈ ball c R)
    (g : ℂ → ℝ) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hM : (pointLocalMaximalEnergy a y c R g x).toReal = 0) : pointPoincareSeries a y R g x = 0 := by
  apply dyadic_series_zero_of_zero_bound
  intro n
  have h := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pointLocalMaximalEnergy_sqrt_average_bound ha y hR hx g hg hgn n)
    (show 0 ≤ (1 / 2 : ℝ) ^ n by positivity))
  simpa only [hM, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] using h

end RepulsiveCoulomb
