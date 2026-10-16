import LeanResearch.RepulsiveCoulomb.PointFormCenter

/-! Literal ball-complement control and the scalar absorption step. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem planar_quadratic_moment_tail {μ : Measure ℂ} {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℝ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hm : Integrable (fun x => ‖x‖ ^ 2 * f x ^ 2) μ) :
    R ^ 2 * (∫ x in (ball (0 : ℂ) R)ᶜ, f x ^ 2 ∂μ) ≤ ∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂μ := by
  have hlocal : R ^ 2 * (∫ x in (ball (0 : ℂ) R)ᶜ, f x ^ 2 ∂μ) ≤
      ∫ x in (ball (0 : ℂ) R)ᶜ, ‖x‖ ^ 2 * f x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hf.integrableOn.const_mul (R ^ 2)) hm.integrableOn measurableSet_ball.compl
    intro x hx
    have hn : R ≤ ‖x‖ := by simpa [mem_ball, dist_zero_right] using hx
    have hs := mul_self_le_mul_self hR.le hn
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hs]) (sq_nonneg (f x))
  exact hlocal.trans (setIntegral_le_integral hm
    (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

theorem quadratic_tail_absorb {C R M L T E K : ℝ}
    (hC : 0 < C) (hR : 2 * C ≤ R ^ 2) (hT : 0 ≤ T)
    (hsplit : L + T = M) (hlocal : L ≤ K * E)
    (htail : R ^ 2 * T ≤ C * (E + M)) : M ≤ (2 * K + 1) * E := by
  have hscaled := mul_le_mul_of_nonneg_right hR hT
  have hcancel : C * (2 * T) ≤ C * (E + M) := by nlinarith only [hscaled, htail]
  have htwo : 2 * T ≤ E + M := (mul_le_mul_iff_right₀ hC).mp hcancel
  nlinarith only [htwo, hsplit, hlocal]

end RepulsiveCoulomb
