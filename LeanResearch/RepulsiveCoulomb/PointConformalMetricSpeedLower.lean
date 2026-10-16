import LeanResearch.RepulsiveCoulomb.PointConformalLocalMetric
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The local analytic flat charts identify physical speed.  Any scalar function
whose local increments dominate the actual conformal distance consequently
dominates that speed at common differentiability points. -/
noncomputable section
open Set Metric Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem norm_deriv_le_of_local_dist_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} {f : ℝ → ℝ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f x)
    (h : ∀ᶠ u in 𝓝 x, dist (g u) (g x) ≤ dist (f u) (f x)) :
    ‖deriv g x‖ ≤ ‖deriv f x‖ := by
  apply le_of_tendsto_of_tendsto hg.hasDerivAt.tendsto_slope.norm
    hf.hasDerivAt.tendsto_slope.norm
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with u hu
  have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ |u - x|⁻¹ by positivity)
  simpa only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, dist_eq_norm] using hh

theorem pointConformalDensity_eq_zero_at_puncture {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) {z : ℂ} (hz : z ∈ pointPunctures a y) :
    pointConformalDensity a y z = 0 := by
  rw [pointConformalDensity, rawPointWeight_eq_pointWeight_zero,
    pointWeight_eq_zero_at_puncture 0 a y hz, Real.sqrt_zero]

theorem pointConformal_physical_speed_le_norm_deriv {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {f : ℝ → ℝ} {x : ℝ}
    (hγ : DifferentiableAt ℝ γ x) (hf : DifferentiableAt ℝ f x)
    (hdom : ∀ᶠ u in 𝓝 x,
      (pointSmoothConformalEDist a y (γ u) (γ x)).toReal ≤ dist (f u) (f x)) :
    pointConformalDensity a y (γ x) * ‖deriv γ x‖ ≤ ‖deriv f x‖ := by
  by_cases hp : γ x ∈ pointPunctures a y
  · rw [pointConformalDensity_eq_zero_at_puncture a y hp, zero_mul]
    exact norm_nonneg _
  obtain ⟨e, hep, _, _, hinv, he⟩ := exists_pointConformal_flat_chart_with_inverse ha y hp
  have hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents 0) standardConeLocations (e z) * ‖deriv e z‖ =
        pointConformalDensity a y z := by
    intro z hz
    refine ⟨(he z hz).1, ?_⟩
    rw [standardCone_density, Real.rpow_zero, one_mul]
    exact (he z hz).2.1
  have hb : ∀ j, 0 ≤ standardConeExponents 0 j := by simp [standardConeExponents]
  obtain ⟨r, hr, _, hmetric⟩ := pointConformal_chart_local_metric_eq ha y hb
    standardConeLocations e hF hinv hep
  have hediff := (he (γ x) hep).1.differentiableAt
  have hbN : ∀ᶠ u in 𝓝 x, γ u ∈ ball (γ x) r :=
    hγ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
  have hdist : ∀ᶠ u in 𝓝 x, dist ((e ∘ γ) u) ((e ∘ γ) x) ≤ dist (f u) (f x) := by
    filter_upwards [hbN, hdom] with u hu hd
    have hm : (pointSmoothConformalEDist a y (γ u) (γ x)).toReal =
        dist (e (γ u)) (e (γ x)) := by
      rw [hmetric _ hu _ (mem_ball_self hr), standardCone_zero_distance,
        ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm']
    exact hm ▸ hd
  have hspeed := norm_deriv_le_of_local_dist_le ((hediff.restrictScalars ℝ).comp x hγ) hf hdist
  have hchain : ‖deriv (e ∘ γ) x‖ = pointConformalDensity a y (γ x) * ‖deriv γ x‖ := by
    rw [fderiv_comp_deriv x (hediff.restrictScalars ℝ) hγ,
      hediff.fderiv_restrictScalars (𝕜 := ℝ)]
    change ‖fderiv ℂ e (γ x) (deriv γ x)‖ = _
    rw [fderiv_eq_smul_deriv, norm_smul, mul_comm, (he (γ x) hep).2.1]
  exact hchain ▸ hspeed

end RepulsiveCoulomb
