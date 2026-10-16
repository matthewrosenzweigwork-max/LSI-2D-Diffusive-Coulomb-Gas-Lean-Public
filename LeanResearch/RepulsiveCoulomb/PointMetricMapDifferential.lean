import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzLength
import LeanResearch.RepulsiveCoulomb.PointConformalMetricSpeedLower

/-! Analytic consequences of actual two-sided point-metric bounds. These do
not construct the uniformizing map. They prove the differential extraction for
any map for which those metric inequalities have already been established. -/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem norm_deriv_le_mul_of_local_dist_le {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → E} {f : ℝ → G} {x C : ℝ} (hC : 0 ≤ C)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ f x)
    (h : ∀ᶠ u in 𝓝 x, dist (g u) (g x) ≤ C * dist (f u) (f x)) :
    ‖deriv g x‖ ≤ C * ‖deriv f x‖ := by
  apply le_of_tendsto_of_tendsto hg.hasDerivAt.tendsto_slope.norm
    (tendsto_const_nhds.mul hf.hasDerivAt.tendsto_slope.norm)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with u hu
  have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ |u - x|⁻¹ by positivity)
  simpa only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, dist_eq_norm,
    mul_assoc, mul_left_comm, mul_comm] using hh

theorem pointConformal_physical_speed_le_mul_norm_deriv {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ f : ℝ → ℂ} {x C : ℝ} (hC : 0 ≤ C)
    (hγ : DifferentiableAt ℝ γ x) (hf : DifferentiableAt ℝ f x)
    (hdom : ∀ᶠ u in 𝓝 x,
      (pointSmoothConformalEDist a y (γ u) (γ x)).toReal ≤ C * dist (f u) (f x)) :
    pointConformalDensity a y (γ x) * ‖deriv γ x‖ ≤ C * ‖deriv f x‖ := by
  by_cases hp : γ x ∈ pointPunctures a y
  · rw [pointConformalDensity_eq_zero_at_puncture a y hp, zero_mul]
    exact mul_nonneg hC (norm_nonneg _)
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
  have hdist : ∀ᶠ u in 𝓝 x, dist ((e ∘ γ) u) ((e ∘ γ) x) ≤ C * dist (f u) (f x) := by
    filter_upwards [hbN, hdom] with u hu hd
    have hm : (pointSmoothConformalEDist a y (γ u) (γ x)).toReal =
        dist (e (γ u)) (e (γ x)) := by
      rw [hmetric _ hu _ (mem_ball_self hr), standardCone_zero_distance,
        ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm']
    exact hm ▸ hd
  have hspeed := norm_deriv_le_mul_of_local_dist_le hC
    ((hediff.restrictScalars ℝ).comp x hγ) hf hdist
  have hchain : ‖deriv (e ∘ γ) x‖ = pointConformalDensity a y (γ x) * ‖deriv γ x‖ := by
    rw [fderiv_comp_deriv x (hediff.restrictScalars ℝ) hγ,
      hediff.fderiv_restrictScalars (𝕜 := ℝ)]
    change ‖fderiv ℂ e (γ x) (deriv γ x)‖ = _
    rw [fderiv_eq_smul_deriv, norm_smul, mul_comm, (he (γ x) hep).2.1]
  exact hchain ▸ hspeed

theorem pointMetricMap_curve_deriv_upper {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤ C * (pointSmoothConformalEDist a y p z).toReal)
    {γ : ℝ → ℂ} {t : ℝ} (hγ : DifferentiableAt ℝ γ t)
    (hFγ : DifferentiableAt ℝ (F ∘ γ) t) :
    ‖deriv (F ∘ γ) t‖ ≤ C * pointConformalDensity a y (γ t) * ‖deriv γ t‖ := by
  have hslope (s : ℝ) : ‖slope (F ∘ γ) t s‖ ≤
      C * Real.sqrt (rawPointBallFactor a y (γ t) ‖γ s - γ t‖) * ‖slope γ t s‖ := by
    have hd : dist (F (γ s)) (F (γ t)) ≤
        C * (Real.sqrt (rawPointBallFactor a y (γ t) ‖γ s - γ t‖) * ‖γ s - γ t‖) := by
      rw [dist_comm]
      exact (hupper (γ t) (γ s)).trans
        (mul_le_mul_of_nonneg_left (pointConformalDistance_segment_upper ha y (γ t) (γ s)) hC)
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ |s - t|⁻¹ by positivity)
    simpa only [slope_def_module, Function.comp_apply, norm_smul, Real.norm_eq_abs,
      abs_inv, dist_eq_norm, mul_assoc, mul_left_comm, mul_comm] using hh
  have hcoef : Tendsto (fun s ↦ Real.sqrt (rawPointBallFactor a y (γ t) ‖γ s - γ t‖))
      (𝓝[≠] t) (𝓝 (pointConformalDensity a y (γ t))) :=
    (pointConformal_segmentCoefficient_tendsto ha y hγ.continuousAt).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hFγ.hasDerivAt.tendsto_slope.norm
    ((tendsto_const_nhds.mul hcoef).mul hγ.hasDerivAt.tendsto_slope.norm)
    (Eventually.of_forall hslope)

theorem pointMetricMap_fderiv_bounds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {L : ℝ} (hL : 0 < L)
    (hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z))
    (hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal)
    {z : ℂ} (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    pointConformalDensity a y z / L * ‖v‖ ≤ ‖fderiv ℝ F z v‖ ∧
      ‖fderiv ℝ F z v‖ ≤ L * pointConformalDensity a y z * ‖v‖ := by
  let γ : ℝ → ℂ := fun t ↦ z + t • v
  have hγ : HasDerivAt γ v 0 := by
    simpa only [γ, one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hFat : HasFDerivAt F (fderiv ℝ F z) (γ 0) := by simpa [γ] using hF.hasFDerivAt
  have hFγ : HasDerivAt (F ∘ γ) (fderiv ℝ F z v) 0 := hFat.comp_hasDerivAt 0 hγ
  have hu := pointMetricMap_curve_deriv_upper ha y hL.le hupper hγ.differentiableAt hFγ.differentiableAt
  have hl := pointConformal_physical_speed_le_mul_norm_deriv ha y hL.le
    hγ.differentiableAt hFγ.differentiableAt
    (Eventually.of_forall fun t ↦ hlower (γ t) (γ 0))
  rw [hγ.deriv, hFγ.deriv] at hl hu
  simp only [γ, zero_smul, add_zero] at hl hu
  refine ⟨?_, hu⟩
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hl)

/-- The metric upper bound gives genuine Euclidean local Lipschitz regularity,
even at the zero-density punctures. -/
theorem pointMetricMap_lipschitzOn_ball {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤ C * (pointSmoothConformalEDist a y p z).toReal)
    (R : ℝ) :
    LipschitzOnWith ⟨C * Real.sqrt (rawPointBallFactor a y 0 (3 * R)), by positivity⟩
      F (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp z hz
  have hp' : ‖p‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hp
  have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hf := Real.sqrt_le_sqrt (rawPointBallFactor_segment_le_bounded ha y hp' hz')
  calc
    dist (F p) (F z) ≤ C * (pointSmoothConformalEDist a y p z).toReal := hupper p z
    _ ≤ C * (Real.sqrt (rawPointBallFactor a y p ‖z - p‖) * ‖z - p‖) :=
      mul_le_mul_of_nonneg_left (pointConformalDistance_segment_upper ha y p z) hC
    _ ≤ C * (Real.sqrt (rawPointBallFactor a y 0 (3 * R)) * ‖z - p‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf (norm_nonneg _)) hC
    _ = _ := by rw [dist_eq_norm']; exact (mul_assoc _ _ _).symm

/-- Rademacher's theorem is applied on an actual countable covering by balls. -/
theorem pointMetricMap_ae_differentiableAt {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤ C * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z := by
  have H (n : ℕ) : ∀ᵐ z ∂volume, z ∈ closedBall (0 : ℂ) (n : ℝ) →
      DifferentiableWithinAt ℝ F (closedBall 0 (n : ℝ)) z :=
    (pointMetricMap_lipschitzOn_ball ha y hC hupper n).ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr H] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hball : z ∈ ball (0 : ℂ) (n : ℝ) := by simpa only [mem_ball, dist_zero_right] using hn
  exact (hz n (ball_subset_closedBall hball)).differentiableAt (closedBall_mem_nhds_of_mem hball)

end RepulsiveCoulomb
