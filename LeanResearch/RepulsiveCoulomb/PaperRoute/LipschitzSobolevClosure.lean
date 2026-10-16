module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.LipschitzMollification
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

@[expose] public section

/-! Weighted dominated convergence transfers a genuine smooth Sobolev inequality
to the actual locally-Lipschitz scalar and actual physical derivative. The
weights may vanish; only local measure finiteness and absolute continuity with
respect to Lebesgue measure are needed. No added loss in constants or dilation. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology NNReal ENNReal ContDiff
namespace RepulsiveCoulomb.PaperRoute

theorem lipschitzMollify_norm_le {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : ℂ) :
    ‖lipschitzMollify f n x‖ ≤ ‖f x‖ + L := by
  have hd := (lipschitzMollify_dist_le hf n x).trans
    (mul_le_mul_of_nonneg_left (lipschitzSmoothingScale_le_one n) L.coe_nonneg)
  rw [mul_one, dist_eq_norm] at hd
  calc
    _ = ‖(lipschitzMollify f n x - f x) + f x‖ := by congr 1; ring
    _ ≤ ‖lipschitzMollify f n x - f x‖ + ‖f x‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem lipschitzMollify_mean_tendsto {μ : Measure ℂ} [IsFiniteMeasure μ]
    {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    Tendsto (fun n => ⨍ x, lipschitzMollify f n x ∂μ) atTop (𝓝 (⨍ x, f x ∂μ)) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : ℂ => B + L)
    (fun n => (lipschitzMollify_contDiff hf.continuous n).continuous.aestronglyMeasurable)
    (integrable_const _) (fun n => by
      filter_upwards [hB] with x hx
      exact (lipschitzMollify_norm_le hf n x).trans (add_le_add hx le_rfl))
    (Eventually.of_forall (lipschitzMollify_tendsto hf.continuous))
  simpa only [average_eq, smul_eq_mul, Function.comp_apply, Pi.sub_apply] using h.const_mul (μ.real univ)⁻¹

/-- Every finite centered moment converges, including the noninteger Sobolev
exponent. The means in the integrands are the genuine varying weighted means. -/
theorem lipschitzMollify_centered_moment_tendsto {μ : Measure ℂ} [IsFiniteMeasure μ]
    {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B)
    {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun n => ⨍ x,
      ‖lipschitzMollify f n x - (⨍ z, lipschitzMollify f n z ∂μ)‖ ^ p ∂μ)
      atTop (𝓝 (⨍ x, ‖f x - (⨍ z, f z ∂μ)‖ ^ p ∂μ)) := by
  let A : ℝ := B + L
  let M : ℝ := (μ.real univ)⁻¹ * (A * μ.real univ)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖lipschitzMollify f n x‖ ≤ A := by
    filter_upwards [hB] with x hx
    exact (lipschitzMollify_norm_le hf n x).trans (add_le_add hx le_rfl)
  have hm (n : ℕ) : ‖(⨍ x, lipschitzMollify f n x ∂μ)‖ ≤ M := by
    rw [average_eq, smul_eq_mul, norm_mul,
      Real.norm_of_nonneg (show 0 ≤ (μ.real univ)⁻¹ by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const (hb n))
      (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have hmean := lipschitzMollify_mean_tendsto hf hB
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n =>
      ‖lipschitzMollify f n x - (⨍ z, lipschitzMollify f n z ∂μ)‖ ^ p)
      atTop (𝓝 (‖f x - (⨍ z, f z ∂μ)‖ ^ p)) := by
    filter_upwards with x
    exact (Real.continuous_rpow_const hp).continuousAt.tendsto.comp
      (((lipschitzMollify_tendsto hf.continuous x).sub hmean).norm)
  have h := tendsto_integral_of_dominated_convergence (fun _ : ℂ => (A+M)^p)
    (fun n => ((Real.continuous_rpow_const hp).comp
      (((lipschitzMollify_contDiff hf.continuous n).continuous.sub continuous_const).norm)).aestronglyMeasurable)
    (integrable_const _) (fun n => by
      filter_upwards [hb n] with x hx
      dsimp only [Function.comp_apply, Pi.sub_apply]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      apply Real.rpow_le_rpow (norm_nonneg _) _ hp
      exact (norm_sub_le _ _).trans (add_le_add hx (hm n))) hlim
  simpa only [average_eq, smul_eq_mul, Function.comp_apply, Pi.sub_apply] using h.const_mul (μ.real univ)⁻¹

/-- Absolute continuity transfers the actual a.e. derivative limit to the
possibly vanishing weight. The unchanged Lipschitz bound dominates energy. -/
theorem lipschitzMollify_energy_tendsto {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ν ≪ volume) {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Tendsto (fun n => ⨍ x, ‖fderiv ℝ (lipschitzMollify f n) x‖ ^ 2 ∂ν)
      atTop (𝓝 (⨍ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν)) := by
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => ‖fderiv ℝ (lipschitzMollify f n) x‖ ^ 2)
      atTop (𝓝 (‖fderiv ℝ f x‖ ^ 2)) := by
    filter_upwards [hν.ae_le (lipschitzMollify_fderiv_ae_tendsto hf)] with x hx
    exact hx.norm.pow 2
  have h := tendsto_integral_of_dominated_convergence (fun _ : ℂ => (L : ℝ)^2)
    (fun n => ((measurable_fderiv ℝ (lipschitzMollify f n)).norm.pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (lipschitzMollify_fderiv_norm_le hf n x) 2)) hlim
  simpa only [average_eq, smul_eq_mul, Function.comp_apply, Pi.sub_apply] using h.const_mul (ν.real univ)⁻¹

/-- A genuine weighted strong-Sobolev closure theorem. All approximation
properties are produced by the preceding explicit mollification lemmas. -/
theorem strong_sobolev_of_lipschitz {μ ν : Measure ℂ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hν : ν ≪ volume)
    {p t C : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hsmooth : ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      (⨍ x, ‖g x - (⨍ z, g z ∂μ)‖ ^ p ∂μ) ^ t ≤
        C * (⨍ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν))
    {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    (⨍ x, ‖f x - (⨍ z, f z ∂μ)‖ ^ p ∂μ) ^ t ≤
      C * (⨍ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν) := by
  have hl := (Real.continuous_rpow_const ht).continuousAt.tendsto.comp
    (lipschitzMollify_centered_moment_tendsto hf hB0 hB hp)
  have hr := (lipschitzMollify_energy_tendsto hν hf).const_mul C
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall (fun n =>
    hsmooth (lipschitzMollify f n) ((lipschitzMollify_contDiff hf.continuous n).of_le (by simp))))

/-- Extension from a closed outer ball preserves both means and the actual
Fréchet derivative on the open outer ball. Neither radius nor constant changes. -/
theorem strong_sobolev_on_balls_of_lipschitzOn
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≪ volume)
    {p t C : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t) (c : ℂ) {r R : ℝ} (hrR : r ≤ R)
    (hsmooth : ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      (⨍ x in ball c r, ‖g x - (⨍ z in ball c r, g z ∂μ)‖ ^ p ∂μ) ^ t ≤
        C * (⨍ x in ball c R, ‖fderiv ℝ g x‖ ^ 2 ∂μ))
    {f : ℂ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (closedBall c R)) :
    (⨍ x in ball c r, ‖f x - (⨍ z in ball c r, f z ∂μ)‖ ^ p ∂μ) ^ t ≤
      C * (⨍ x in ball c R, ‖fderiv ℝ f x‖ ^ 2 ∂μ) := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  have hinner : ball c r ⊆ closedBall c R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hrR)
  have hfi (S : ℝ) : IsFiniteMeasure (μ.restrict (ball c S)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_mono (ball_subset_closedBall : ball c S ⊆ closedBall c S)).trans_lt
        (isCompact_closedBall c S).measure_lt_top⟩
  let := hfi r
  let := hfi R
  obtain ⟨B, hB⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hg.continuous.continuousOn
  have hbound : ∀ᵐ x ∂μ.restrict (ball c r), ‖g x‖ ≤ max 0 B := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hB x (ball_subset_closedBall hx)).trans (le_max_right _ _)
  have h := strong_sobolev_of_lipschitz
    ((Measure.absolutelyContinuous_restrict (μ := μ) (s := ball c R)).trans hμ)
    hp ht hsmooth hg (le_max_left 0 B) hbound
  have hm : (⨍ z in ball c r, f z ∂μ) = (⨍ z in ball c r, g z ∂μ) := by
    simp only [setAverage_eq]
    congr 1
    exact setIntegral_congr_fun measurableSet_ball (heq.mono hinner)
  have hl : (⨍ x in ball c r, ‖f x - (⨍ z in ball c r, f z ∂μ)‖ ^ p ∂μ) =
      (⨍ x in ball c r, ‖g x - (⨍ z in ball c r, g z ∂μ)‖ ^ p ∂μ) := by
    rw [hm]
    simp only [setAverage_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [heq (hinner hx)]
  have hr : (⨍ x in ball c R, ‖fderiv ℝ f x‖ ^ 2 ∂μ) =
      (⨍ x in ball c R, ‖fderiv ℝ g x‖ ^ 2 ∂μ) := by
    simp only [setAverage_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hlocal : f =ᶠ[𝓝 x] g := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact heq (ball_subset_closedBall hy)
    dsimp only
    rw [hlocal.fderiv_eq]
  rw [hl, hr]
  exact h

end RepulsiveCoulomb.PaperRoute
