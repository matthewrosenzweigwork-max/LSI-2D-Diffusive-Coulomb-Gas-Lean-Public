import LeanResearch.RepulsiveCoulomb.PointConformalTopology
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Sharp local slope bounds for the actual finite-point conformal distance.
These apply to every nonnegative finite point configuration, including at the
zero-density punctures, and are inputs to the rectifiable-length identification.
No sector existence, curvature comparison, or triangulation is assumed. -/
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem rawPointBallFactor_continuous_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    Continuous (rawPointBallFactor a y p) := by
  unfold rawPointBallFactor
  apply continuous_finset_prod
  intro j hj
  exact (Real.continuous_rpow_const (ha j)).comp (continuous_id.add continuous_const)

@[simp] theorem rawPointBallFactor_zero_radius {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (p : ℂ) : rawPointBallFactor a y p 0 = rawPointWeight a y p := by
  simp [rawPointBallFactor, rawPointWeight]

theorem pointConformalDistance_segment_upper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p z : ℂ) :
    (pointSmoothConformalEDist a y p z).toReal ≤
      Real.sqrt (rawPointBallFactor a y p ‖z - p‖) * ‖z - p‖ := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    (pointSmoothConformalEDist_segment_upper ha y p z)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (norm_nonneg _)] using h

theorem pointConformalDistance_abs_sub_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p z c : ℂ) :
    |(pointSmoothConformalEDist a y p c).toReal -
        (pointSmoothConformalEDist a y z c).toReal| ≤
      (pointSmoothConformalEDist a y p z).toReal :=
  @abs_dist_sub_le ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p z c

theorem pointConformalDistance_abs_sub_segment_upper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p z c : ℂ) :
    |(pointSmoothConformalEDist a y z c).toReal -
        (pointSmoothConformalEDist a y p c).toReal| ≤
      Real.sqrt (rawPointBallFactor a y p ‖z - p‖) * ‖z - p‖ := by
  have h := pointConformalDistance_abs_sub_le ha y z p c
  rw [pointSmoothConformalEDist_comm a y z p] at h
  exact h.trans (pointConformalDistance_segment_upper ha y p z)

theorem pointConformal_segmentCoefficient_tendsto {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {t : ℝ}
    (hγ : ContinuousAt γ t) :
    Tendsto (fun s ↦ Real.sqrt (rawPointBallFactor a y (γ t) ‖γ s - γ t‖))
      (𝓝 t) (𝓝 (pointConformalDensity a y (γ t))) := by
  have hr : Tendsto (fun s ↦ ‖γ s - γ t‖) (𝓝 t) (𝓝 0) := by
    simpa using (hγ.sub (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ γ t) t)).norm.tendsto
  have h := (Real.continuous_sqrt.tendsto (rawPointBallFactor a y (γ t) 0)).comp
    (((rawPointBallFactor_continuous_radius ha y (γ t)).tendsto 0).comp hr)
  simpa only [Function.comp_def, rawPointBallFactor_zero_radius, pointConformalDensity] using h

/-- Along any differentiable Euclidean curve, the distance-to-a-point function
has derivative bounded by physical weighted speed. No differentiability of the
distance function is imposed: its total derivative is zero where undefined. -/
theorem pointConformalDistance_deriv_norm_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {γ : ℝ → ℂ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) :
    ‖deriv (fun s ↦ (pointSmoothConformalEDist a y (γ s) c).toReal) t‖ ≤
      pointConformalDensity a y (γ t) * ‖deriv γ t‖ := by
  let f : ℝ → ℝ := fun s ↦ (pointSmoothConformalEDist a y (γ s) c).toReal
  by_cases hf : DifferentiableAt ℝ f t
  · have hslope (s : ℝ) : ‖slope f t s‖ ≤
        Real.sqrt (rawPointBallFactor a y (γ t) ‖γ s - γ t‖) * ‖slope γ t s‖ := by
      have h := mul_le_mul_of_nonneg_left
        (pointConformalDistance_abs_sub_segment_upper ha y (γ t) (γ s) c)
        (show 0 ≤ |s - t|⁻¹ by positivity)
      simpa only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, abs_mul,
        smul_eq_mul, f, mul_assoc, mul_left_comm, mul_comm] using h
    have hf_lim := hf.hasDerivAt.tendsto_slope.norm
    have hγ_lim := hγ.hasDerivAt.tendsto_slope.norm
    have hcoef : Tendsto (fun s ↦ Real.sqrt (rawPointBallFactor a y (γ t) ‖γ s - γ t‖))
        (𝓝[≠] t) (𝓝 (pointConformalDensity a y (γ t))) :=
      (pointConformal_segmentCoefficient_tendsto ha y hγ.continuousAt).mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hf_lim (hcoef.mul hγ_lim) (Eventually.of_forall hslope)
  · rw [show (fun s ↦ (pointSmoothConformalEDist a y (γ s) c).toReal) = f by rfl,
      deriv_zero_of_not_differentiableAt hf, norm_zero]
    exact mul_nonneg (pointConformalDensity_nonneg a y _) (norm_nonneg _)

end RepulsiveCoulomb
