import LeanResearch.RepulsiveCoulomb.PointOscillationTransfer

/-! The integrated part of the transfer, still explicitly conditional on the
unproved double-average gradient estimate. No actual Poincare conclusion is
claimed without that input. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointTransferPrefactor (Q K : ℝ) : ℝ :=
  K * rawPointDoublingConstant Q *
    (4 * rawPointDoublingConstant (2 * Q) + 2 * rawPointInitialMeanConstant (2 * Q))

theorem pointTransferPrefactor_nonneg (Q : ℝ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ pointTransferPrefactor Q K := by
  unfold pointTransferPrefactor
  have hD := rawPointDoublingConstant_pos Q
  have hD2 := rawPointDoublingConstant_pos (2 * Q)
  have hA := rawPointInitialMeanConstant_pos (2 * Q)
  positivity

theorem rawPoint_integrated_transfer_of_double_average_bound {m : ℕ} {Q K : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hK : 0 ≤ K) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hO : ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y f c r ≤
        K * r * ⨍ z in ball c (2 * r), g z ∂rawPointMeasure a y)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in ball c R,
      ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure (fun j => 2 * a j) y)‖ ∂rawPointMeasure a y) ≤
      ENNReal.ofReal (R * pointTransferPrefactor Q K) *
        ∫⁻ z in ball c (5 * R), ENNReal.ofReal (g z) ∂rawPointMeasure a y := by
  let μ := rawPointMeasure a y
  let S : ℂ → ℝ≥0∞ := fun x => ∑' n : ℕ, ENNReal.ofReal (dyadicBallRadius (2 * R) n *
    ⨍ z in ball x (2 * dyadicBallRadius (2 * R) n), g z ∂μ)
  let T : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (⨍ z in ball x (4 * R), g z ∂μ)
  let A := ENNReal.ofReal (K * rawPointDoublingConstant (2 * Q))
  let B := ENNReal.ofReal (2 * R * K * rawPointInitialMeanConstant (2 * Q))
  let G := ∫⁻ z in ball c (5 * R), ENNReal.ofReal (g z) ∂μ
  have hS : Measurable S := by
    apply Measurable.tsum
    intro n
    simp_rw [ENNReal.ofReal_mul (dyadicBallRadius_pos (show 0 < 2 * R by positivity) n).le]
    exact (measurable_rawPoint_ofReal_average ha y g hg hgn _).const_mul _
  have hpoint := fun x hx => rawPoint_pointwise_transfer_of_double_average_bound ha hQ hK y f g hf hO c hR (x := x) hx
  have hD := rawPointDoublingConstant_pos Q
  have hD2 := rawPointDoublingConstant_pos (2 * Q)
  have hA2 := rawPointInitialMeanConstant_pos (2 * Q)
  calc
    _ ≤ ∫⁻ x in ball c R, A * S x + B * T x ∂μ :=
      setLIntegral_mono' measurableSet_ball hpoint
    _ = A * (∫⁻ x in ball c R, S x ∂μ) + B * (∫⁻ x in ball c R, T x ∂μ) := by
      rw [lintegral_add_left (hS.const_mul A), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ A * (ENNReal.ofReal (4 * R * rawPointDoublingConstant Q) * G) +
        B * (ENNReal.ofReal (rawPointDoublingConstant Q) * G) := by
      apply add_le_add
      · exact mul_le_mul' le_rfl (rawPointMeasure_dyadic_average_fubini ha hQ y c hR g hg hgn)
      · exact mul_le_mul' le_rfl (rawPointMeasure_average_fubini_bound ha hQ y c (by positivity : 0 < 4 * R) le_rfl g hg hgn)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← add_mul]
      dsimp only [A, B]
      rw [← ENNReal.ofReal_mul (mul_nonneg hK hD2.le),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by positivity) hK) hA2.le),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      unfold pointTransferPrefactor
      ring

end RepulsiveCoulomb
