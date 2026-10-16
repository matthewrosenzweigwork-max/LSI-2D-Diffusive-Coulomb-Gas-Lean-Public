module

public import LeanResearch.RepulsiveCoulomb.PointAverageFubini
public import LeanResearch.RepulsiveCoulomb.PointDyadicOscillation

@[expose] public section

/-! Summation and averaging of the actual dyadic ball averages. All exchanges
use nonnegative integrals and proved measurability, without an assumed finite
pointwise series or an unproved gradient inequality. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem measurable_rawPoint_ofReal_average {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (g : ℂ → ℝ) (hg : Continuous g)
    (hn : ∀ z, 0 ≤ g z) (r : ℝ) :
    Measurable (fun x => ENNReal.ofReal (⨍ z in ball x r, g z ∂rawPointMeasure a y)) := by
  letI := rawPointMeasure_locallyFinite ha y
  simp_rw [rawPointMeasure_ofReal_average_eq_kernel ha y g hg hn]
  exact ((measurable_rawPointAveragingKernel ha y r).ennreal_ofReal.mul
    (hg.measurable.ennreal_ofReal.comp measurable_snd)).lintegral_prod_right'

theorem rawPointMeasure_average_series_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) (R : ℝ) (r b : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrR : ∀ n, r n ≤ 4 * R)
    (hb : ∀ n, 0 ≤ b n) (g : ℂ → ℝ) (hg : Continuous g) (hn : ∀ z, 0 ≤ g z) :
    (∫⁻ x in ball c R, ∑' n : ℕ,
      ENNReal.ofReal (b n * ⨍ z in ball x (r n), g z ∂rawPointMeasure a y) ∂rawPointMeasure a y) ≤
      (∑' n : ℕ, ENNReal.ofReal (b n)) * ENNReal.ofReal (rawPointDoublingConstant Q) *
        ∫⁻ z in ball c (5 * R), ENNReal.ofReal (g z) ∂rawPointMeasure a y := by
  simp_rw [ENNReal.ofReal_mul (hb _)]
  rw [lintegral_tsum (fun n =>
    ((measurable_rawPoint_ofReal_average ha y g hg hn (r n)).const_mul _).aemeasurable)]
  calc
    _ = ∑' n : ℕ, ENNReal.ofReal (b n) *
        ∫⁻ x in ball c R, ENNReal.ofReal (⨍ z in ball x (r n), g z ∂rawPointMeasure a y) ∂rawPointMeasure a y := by
      apply tsum_congr
      intro n
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (b n) *
        (ENNReal.ofReal (rawPointDoublingConstant Q) *
          ∫⁻ z in ball c (5 * R), ENNReal.ofReal (g z) ∂rawPointMeasure a y) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact mul_le_mul' le_rfl (rawPointMeasure_average_fubini_bound ha hQ y c (hr n) (hrR n) g hg hn)
    _ = _ := by rw [ENNReal.tsum_mul_right, mul_assoc]

theorem dyadicBallRadius_tsum {R : ℝ} (hR : 0 ≤ R) :
    (∑' n : ℕ, ENNReal.ofReal (dyadicBallRadius R n)) = ENNReal.ofReal (2 * R) := by
  have h : HasSum (dyadicBallRadius R) (2 * R) := by
    change HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * R) (2 * R)
    exact hasSum_geometric_two.mul_right R
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by unfold dyadicBallRadius; positivity) h.summable,
    h.tsum_eq]

theorem dyadicBallRadius_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) : dyadicBallRadius R n ≤ R := by
  apply mul_le_of_le_one_left hR
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem rawPointMeasure_dyadic_average_fubini {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℝ) (hg : Continuous g) (hn : ∀ z, 0 ≤ g z) :
    (∫⁻ x in ball c R, ∑' n : ℕ,
      ENNReal.ofReal (dyadicBallRadius (2 * R) n *
        ⨍ z in ball x (2 * dyadicBallRadius (2 * R) n), g z ∂rawPointMeasure a y) ∂rawPointMeasure a y) ≤
      ENNReal.ofReal (4 * R * rawPointDoublingConstant Q) *
        ∫⁻ z in ball c (5 * R), ENNReal.ofReal (g z) ∂rawPointMeasure a y := by
  have hp (n : ℕ) : 0 < dyadicBallRadius (2 * R) n := dyadicBallRadius_pos (by positivity) n
  have h := rawPointMeasure_average_series_bound ha hQ y c R
    (fun n => 2 * dyadicBallRadius (2 * R) n) (dyadicBallRadius (2 * R))
    (fun n => by have := hp n; positivity)
    (fun n => by have := dyadicBallRadius_le (show 0 ≤ 2 * R by positivity) n; linarith)
    (fun n => (hp n).le) g hg hn
  rw [dyadicBallRadius_tsum (by positivity), show 2 * (2 * R) = 4 * R by ring,
    ← ENNReal.ofReal_mul (by positivity)] at h
  exact h

end RepulsiveCoulomb
