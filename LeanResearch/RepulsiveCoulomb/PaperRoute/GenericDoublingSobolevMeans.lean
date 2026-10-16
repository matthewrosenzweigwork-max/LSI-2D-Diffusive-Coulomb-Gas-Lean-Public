import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericDoublingSobolevBasics

/-! Dyadic telescoping directly in terms of mean-centered L1 oscillation.
These are actual identities and inequalities, with no Poincare hypothesis. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute


/-- Direct twofold real-mass control from the same supplied global D. -/
theorem GlobalDoublingWith.real_ball_double_le {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    μ.real (ball c (2 * r)) ≤ D * μ.real (ball c r) := by
  simpa only [pow_one] using hD.real_ball_pow_two_le hμ c hr 1

theorem GlobalDoublingWith.shifted_ball_real {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (c : ℂ) {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball c R) :
    μ.real (ball x (2 * R)) ≤ D ^ 2 * μ.real (ball c R) := by
  have hsub : ball x (2 * R) ⊆ ball c (4 * R) := by
    apply ball_subset_ball'
    have hxc := mem_ball.mp hx
    linarith
  exact (ENNReal.toReal_mono (hμ.ball_lt_top c (4 * R)).ne (measure_mono hsub)).trans
    (hD.real_ball_four_le hμ c hR)

theorem GlobalDoublingWith.dyadic_mean_oscillation {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal ‖f c - (⨍ z in ball c R, f z ∂μ)‖ ≤
      ∑' n : ℕ, ENNReal.ofReal (D *
        ⨍ x in ball c (doublingMeanRadius R n),
          ‖f x - (⨍ z in ball c (doublingMeanRadius R n), f z ∂μ)‖ ∂μ) := by
  let u : ℕ → ℝ := fun n => ⨍ z in ball c (doublingMeanRadius R n), f z ∂μ
  have hlim : Tendsto u atTop (𝓝 (f c)) :=
    (hμ.average_tendsto f hf c).comp (doublingMeanRadius_tendsto hR)
  have hstep (n : ℕ) : ‖u (n + 1) - u n‖ ≤ D *
      ⨍ x in ball c (doublingMeanRadius R n),
        ‖f x - (⨍ z in ball c (doublingMeanRadius R n), f z ∂μ)‖ ∂μ := by
    have hr := doublingMeanRadius_pos hR n
    have hs := doublingMeanRadius_pos hR (n + 1)
    have he : 2 * doublingMeanRadius R (n + 1) = doublingMeanRadius R n := by
      simp only [doublingMeanRadius, pow_succ]
      ring
    have hST : ball c (doublingMeanRadius R (n + 1)) ⊆ ball c (doublingMeanRadius R n) :=
      ball_subset_ball (by linarith)
    have h := norm_nested_average_difference_le_generic μ hST
      (hμ c _ hs).1.ne' (hμ.ball_lt_top c _).ne
      (hμ c _ hr).1.ne' (hμ.ball_lt_top c _).ne
      (hμ.continuous_ball_integrable hf c _)
    have hmass := hD.real_ball_double_le hμ c hs
    rw [he] at hmass
    have hpos : 0 < μ.real (ball c (doublingMeanRadius R (n + 1))) :=
      ENNReal.toReal_pos (hμ c _ hs).1.ne' (hμ.ball_lt_top c _).ne
    have hratio : μ.real (ball c (doublingMeanRadius R n)) /
        μ.real (ball c (doublingMeanRadius R (n + 1))) ≤ D :=
      (div_le_iff₀ hpos).mpr hmass
    exact h.trans (mul_le_mul_of_nonneg_right hratio
      (average_nonneg (fun x => norm_nonneg _)))
  have ht := edist_le_tsum_of_edist_le_of_tendsto₀
    (fun n : ℕ => ENNReal.ofReal (D *
      ⨍ x in ball c (doublingMeanRadius R n),
        ‖f x - (⨍ z in ball c (doublingMeanRadius R n), f z ∂μ)‖ ∂μ))
    (fun n => by simpa only [edist_dist, dist_eq_norm'] using ENNReal.ofReal_le_ofReal (hstep n)) hlim
  simpa only [u, doublingMeanRadius, pow_zero, one_mul, edist_dist, dist_eq_norm'] using ht

theorem GlobalDoublingWith.initial_mean_difference_centered {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {x : ℂ} (hx : x ∈ ball c R) :
    ‖(⨍ z in ball c R, f z ∂μ) - (⨍ z in ball x (2 * R), f z ∂μ)‖ ≤
      D ^ 2 * ⨍ z in ball x (2 * R),
        ‖f z - (⨍ w in ball x (2 * R), f w ∂μ)‖ ∂μ := by
  have h2R : 0 < 2 * R := by positivity
  have hsub : ball c R ⊆ ball x (2 * R) := by
    apply ball_subset_ball'
    have hcx : dist c x < R := by simpa only [dist_comm] using mem_ball.mp hx
    linarith
  have h := norm_nested_average_difference_le_generic μ hsub
    (hμ c _ hR).1.ne' (hμ.ball_lt_top c R).ne
    (hμ x _ h2R).1.ne' (hμ.ball_lt_top x (2 * R)).ne
    (hμ.continuous_ball_integrable hf x (2 * R))
  have hpos : 0 < (μ).real (ball c R) :=
    ENNReal.toReal_pos (hμ c _ hR).1.ne' (hμ.ball_lt_top c R).ne
  have hr : (μ).real (ball x (2 * R)) / (μ).real (ball c R) ≤
      D ^ 2 :=
    (div_le_iff₀ hpos).mpr (hD.shifted_ball_real hμ c hR hx)
  exact h.trans (mul_le_mul_of_nonneg_right hr (average_nonneg (fun z => norm_nonneg _)))

theorem GlobalDoublingWith.global_dyadic_mean_oscillation {μ : Measure ℂ} {D : ℝ}
    (hD : GlobalDoublingWith μ D) (hμ : PositiveFiniteBalls μ)
    (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {x : ℂ} (hx : x ∈ ball c R) :
    ENNReal.ofReal ‖f x - (⨍ z in ball c R, f z ∂μ)‖ ≤
      (∑' n : ℕ, ENNReal.ofReal (D *
        ⨍ z in ball x (doublingMeanRadius (2 * R) n),
          ‖f z - (⨍ w in ball x (doublingMeanRadius (2 * R) n), f w ∂μ)‖ ∂μ)) +
      ENNReal.ofReal (D ^ 2 *
        ⨍ z in ball x (2 * R), ‖f z - (⨍ w in ball x (2 * R), f w ∂μ)‖ ∂μ) := by
  let A := ⨍ z in ball c R, f z ∂μ
  let B := ⨍ z in ball x (2 * R), f z ∂μ
  have ht : ‖f x - A‖ ≤ ‖f x - B‖ + ‖A - B‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f x - B) (A - B)
  calc
    _ ≤ ENNReal.ofReal (‖f x - B‖ + ‖A - B‖) := ENNReal.ofReal_le_ofReal ht
    _ = ENNReal.ofReal ‖f x - B‖ + ENNReal.ofReal ‖A - B‖ :=
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := add_le_add (hD.dyadic_mean_oscillation hμ f hf x (by positivity))
      (ENNReal.ofReal_le_ofReal (hD.initial_mean_difference_centered hμ f hf c hR hx))

end RepulsiveCoulomb.PaperRoute
