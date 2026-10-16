import LeanResearch.RepulsiveCoulomb.PointMomentTail

/-! Quadratic moment tails in any real normed configuration space.
Both the mass and moment integrability are explicit, excluding Bochner defaults. -/
noncomputable section
open Set MeasureTheory Metric Filter
namespace RepulsiveCoulomb

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem repulsive_quadratic_moment_tail {μ : Measure E} {R : ℝ} (hR : 0 < R)
    (f : E → ℝ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hm : Integrable (fun x => ‖x‖ ^ 2 * f x ^ 2) μ) :
    R ^ 2 * (∫ x in (ball (0 : E) R)ᶜ, f x ^ 2 ∂μ) ≤
      ∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂μ := by
  have hlocal : R ^ 2 * (∫ x in (ball (0 : E) R)ᶜ, f x ^ 2 ∂μ) ≤
      ∫ x in (ball (0 : E) R)ᶜ, ‖x‖ ^ 2 * f x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hf.integrableOn.const_mul (R ^ 2))
      hm.integrableOn measurableSet_ball.compl
    intro x hx
    have hn : R ≤ ‖x‖ := by simpa [mem_ball, dist_zero_right] using hx
    have hs := mul_self_le_mul_self hR.le hn
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hs]) (sq_nonneg (f x))
  exact hlocal.trans (setIntegral_le_integral hm
    (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

theorem repulsive_quadratic_moment_tail_le {μ : Measure E} {R C : ℝ} (hR : 0 < R)
    (f : E → ℝ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hm : Integrable (fun x => ‖x‖ ^ 2 * f x ^ 2) μ)
    (hC : (∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂μ) ≤ C) :
    (∫ x in (ball (0 : E) R)ᶜ, f x ^ 2 ∂μ) ≤ C / R ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  simpa only [mul_comm] using (repulsive_quadratic_moment_tail hR f hf hm).trans hC

end RepulsiveCoulomb
