import LeanResearch.RepulsiveCoulomb.PointIntegratedTransfer

/-! Normalized L1 transfer with actual raw point measures. Every conclusion in
this file remains explicitly conditional on the displayed double-average input.
The missing David--Semmes input is not discharged or hidden by this interface. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointMeanTransferConstant (Q K : ℝ) : ℝ :=
  2 * pointTransferPrefactor Q K * rawPointGrowthConstant Q * (5 : ℝ) ^ (Q + 2)

theorem pointMeanTransferConstant_pos (Q : ℝ) {K : ℝ} (hK : 0 < K) : 0 < pointMeanTransferConstant Q K := by
  unfold pointMeanTransferConstant pointTransferPrefactor
  have hD := rawPointDoublingConstant_pos Q
  have hD2 := rawPointDoublingConstant_pos (2 * Q)
  have hA := rawPointInitialMeanConstant_pos (2 * Q)
  have hG := rawPointGrowthConstant_pos Q
  positivity

theorem rawPoint_real_transfer_of_double_average_bound {m : ℕ} {Q K : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hK : 0 ≤ K) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hO : ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y f c r ≤
        K * r * ⨍ z in ball c (2 * r), g z ∂rawPointMeasure a y)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball c R,
      ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure (fun j => 2 * a j) y)‖ ∂rawPointMeasure a y) ≤
      R * pointTransferPrefactor Q K * ∫ z in ball c (5 * R), g z ∂rawPointMeasure a y := by
  have hI := rawPointMeasure_continuous_ball_integrable ha y
    (f := fun x => ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure (fun j => 2 * a j) y)‖)
    (by fun_prop) c R
  have hG := rawPointMeasure_continuous_ball_integrable ha y hg c (5 * R)
  have h := rawPoint_integrated_transfer_of_double_average_bound ha hQ hK y f g hf hg hgn hO c hR
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall (fun _ => norm_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hG (Eventually.of_forall hgn),
    ← ENNReal.ofReal_mul (mul_nonneg hR.le (pointTransferPrefactor_nonneg Q hK))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hR.le (pointTransferPrefactor_nonneg Q hK))
    (integral_nonneg hgn))).mp h

theorem rawPoint_mean_transfer_of_double_average_bound {m : ℕ} {Q K : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hK : 0 < K) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hO : ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y f c r ≤
        K * r * ⨍ z in ball c (2 * r), g z ∂rawPointMeasure a y)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      pointMeanTransferConstant Q K * R * ⨍ z in ball c (5 * R), g z ∂rawPointMeasure a y := by
  let μ := rawPointMeasure a y
  let A := ⨍ z in ball c R, f z ∂rawPointMeasure (fun j => 2 * a j) y
  let M := μ.real (ball c R)
  let N := μ.real (ball c (5 * R))
  let H := rawPointGrowthConstant Q * (5 : ℝ) ^ (Q + 2)
  let J := ∫ z in ball c (5 * R), g z ∂μ
  have hM : 0 < M := ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c hR).ne'
    (rawPointMeasure_ball_lt_top ha y c R).ne
  have hN : 0 < N := ENNReal.toReal_pos (rawPointMeasure_ball_pos ha y c (show 0 < 5 * R by positivity)).ne'
    (rawPointMeasure_ball_lt_top ha y c (5 * R)).ne
  have hJ : 0 ≤ J := integral_nonneg hgn
  have hmass : N ≤ H * M := rawPointMeasure_growth_real ha hQ y c hR (by norm_num : (1 : ℝ) ≤ 5)
  have hinv : M⁻¹ ≤ H * N⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hN).mpr
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hM).mpr hmass
  have hbound := rawPoint_real_transfer_of_double_average_bound ha hQ hK.le y f g hf hg hgn hO c hR
  have hnorm : (⨍ x in ball c R, ‖f x - A‖ ∂μ) ≤
      R * pointTransferPrefactor Q K * H * (⨍ z in ball c (5 * R), g z ∂μ) := by
    simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change M⁻¹ * (∫ x in ball c R, ‖f x - A‖ ∂μ) ≤ R * pointTransferPrefactor Q K * H * (N⁻¹ * J)
    calc
      _ ≤ M⁻¹ * (R * pointTransferPrefactor Q K * J) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hM.le)
      _ = (R * pointTransferPrefactor Q K) * (M⁻¹ * J) := by ring
      _ ≤ (R * pointTransferPrefactor Q K) * ((H * N⁻¹) * J) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv hJ)
          (mul_nonneg hR.le (pointTransferPrefactor_nonneg Q hK.le))
      _ = _ := by ring
  have hcenter := setAverage_norm_centered_le_twice μ (rawPointMeasure_ball_pos ha y c hR).ne'
    (rawPointMeasure_ball_lt_top ha y c R).ne (rawPointMeasure_continuous_ball_integrable ha y hf c R) A
  apply hcenter.trans
  have h := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  unfold pointMeanTransferConstant H
  ring

end RepulsiveCoulomb
