module

public import LeanResearch.RepulsiveCoulomb.PointDavidSemmesTransfer

@[expose] public section

/-! A complete quantitative implication from the explicitly displayed, still
unproved David--Semmes input to weak(1,2) Poincare for actual C1 observables.
The gradient is the physical real Euclidean gradient already used by the
campaign. This implication is NOT completion of the local Poincare theorem. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_average_le_rms {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (g : ℂ → ℝ) (hg : Continuous g)
    (hgn : ∀ z, 0 ≤ g z) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (⨍ z in ball c r, g z ∂rawPointMeasure a y) ≤
      Real.sqrt (⨍ z in ball c r, g z ^ 2 ∂rawPointMeasure a y) := by
  let μ := (rawPointMeasure a y).restrict (ball c r)
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using rawPointMeasure_ball_lt_top ha y c r⟩
  letI : NeZero μ := ⟨by
    intro h
    have he := congrArg (fun ν : Measure ℂ => ν univ) h
    exact (rawPointMeasure_ball_pos ha y c hr).ne' (by simpa [μ] using he)⟩
  have hi : Integrable g μ := rawPointMeasure_continuous_ball_integrable ha y hg c r
  have hi2 : Integrable (fun z => g z ^ 2) μ := rawPointMeasure_continuous_ball_integrable ha y (hg.pow 2) c r
  have h := (convexOn_pow (𝕜 := ℝ) 2).map_average_le (μ := μ)
    (continuous_pow 2).continuousOn isClosed_Ici (Eventually.of_forall hgn) hi hi2
  exact Real.le_sqrt_of_sq_le h

theorem rawPoint_physical_weak_one_two_of_DavidSemmes {m : ℕ} {Q C : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hC : 0 < C) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f)
    (hDS : ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      rawPointDoubleAverageOscillation (fun j => 2 * a j) y f c r ≤
        C * ((rawPointMeasure a y).real (ball c (2 * r)) /
          Real.sqrt ((rawPointMeasure (fun j => 2 * a j) y).real (ball c r))) *
        ⨍ z in ball c (2 * r), ‖gradient f z‖ ∂rawPointMeasure a y)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R, ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      pointMeanTransferConstant Q (C * rawPointDoublingConstant Q * Real.sqrt Real.pi) * R *
        Real.sqrt (⨍ z in ball c (5 * R), ‖gradient f z‖ ^ 2 ∂rawPointMeasure a y) := by
  have hg : Continuous (fun z => ‖gradient f z‖) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hf.continuous_fderiv one_ne_zero).norm
  have hK : 0 < C * rawPointDoublingConstant Q * Real.sqrt Real.pi :=
    mul_pos (mul_pos hC (rawPointDoublingConstant_pos Q)) (Real.sqrt_pos.mpr Real.pi_pos)
  have h := rawPoint_mean_transfer_of_DavidSemmes_estimate ha hQ hC y f
    (fun z => ‖gradient f z‖) hf.continuous hg (fun z => norm_nonneg _) hDS c hR
  exact h.trans (mul_le_mul_of_nonneg_left
    (rawPointMeasure_average_le_rms ha y _ hg (fun z => norm_nonneg _) c (by positivity : 0 < 5 * R))
    (mul_nonneg (pointMeanTransferConstant_pos Q hK).le hR.le))

end RepulsiveCoulomb
