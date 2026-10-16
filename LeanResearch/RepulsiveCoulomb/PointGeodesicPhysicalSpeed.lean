import LeanResearch.RepulsiveCoulomb.PointGeodesicAnalytic
import LeanResearch.RepulsiveCoulomb.MetricSpeedDerivative

/-! The constant metric speed equals the physical density-weighted Euclidean
speed at every interior parameter away from positive punctures. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointConformal_geodesic_physical_speed {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y) :
    pointConformalDensity a y (γ t) * ‖deriv γ t‖ = L := by
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
  have hg := (pointConformal_geodesic_analyticAt ha y γ hc L hgeo ht hp).differentiableAt
  have hf := (he (γ t) hep).1.differentiableAt
  have htN : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds ht.1 ht.2
  have hbN : ∀ᶠ s in 𝓝 t, γ s ∈ ball (γ t) r :=
    (isOpen_ball.preimage hc).mem_nhds (mem_ball_self hr)
  have hN : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) 1 ∧ γ s ∈ ball (γ t) r := htN.and hbN
  have hscaled : ∀ᶠ s in 𝓝 t, dist ((e ∘ γ) s) ((e ∘ γ) t) = |s - t| * L := by
    filter_upwards [hN] with s hs
    have hd : (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist (e (γ s)) (e (γ t)) := by
      rw [hmetric _ hs.2 _ (mem_ball_self hr), standardCone_zero_distance,
        ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm']
    change dist (e (γ s)) (e (γ t)) = _
    rw [← hd, hgeo s ⟨hs.1.1.le, hs.1.2.le⟩ t ⟨ht.1.le, ht.2.le⟩, abs_sub_comm]
  have hspeed := norm_deriv_eq_of_local_scaled_dist ((hf.restrictScalars ℝ).comp t hg) hscaled
  have hchain : ‖deriv (e ∘ γ) t‖ = pointConformalDensity a y (γ t) * ‖deriv γ t‖ := by
    rw [fderiv_comp_deriv t (hf.restrictScalars ℝ) hg, hf.fderiv_restrictScalars (𝕜 := ℝ)]
    change ‖fderiv ℂ e (γ t) (deriv γ t)‖ = _
    rw [fderiv_eq_smul_deriv, norm_smul, mul_comm, (he (γ t) hep).2.1]
  exact hchain.symm.trans hspeed

end RepulsiveCoulomb
