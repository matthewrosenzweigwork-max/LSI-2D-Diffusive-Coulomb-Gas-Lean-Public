import LeanResearch.RepulsiveCoulomb.PointGeodesicFlatness

/-! A flat metric chart with its analytic inverse retained, and the exact affine
parameter formula for a geodesic segment lying in such a chart. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_flat_analytic_metric_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ, 0 < r ∧ e p = 0 ∧ ball p r ⊆ e.source ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z) ∧
      ∀ u ∈ ball p r, ∀ v ∈ ball p r,
        (pointSmoothConformalEDist a y u v).toReal = dist (e u) (e v) := by
  obtain ⟨e, hep, he0, _, hinv, he⟩ := exists_pointConformal_flat_chart_with_inverse ha y hp
  have hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents 0) standardConeLocations (e z) * ‖deriv e z‖ =
        pointConformalDensity a y z := by
    intro z hz
    refine ⟨(he z hz).1, ?_⟩
    rw [standardCone_density, Real.rpow_zero, one_mul]
    exact (he z hz).2.1
  have hb : ∀ j, 0 ≤ standardConeExponents 0 j := by simp [standardConeExponents]
  obtain ⟨r, hr, hsub, hmetric⟩ := pointConformal_chart_local_metric_eq ha y hb
    standardConeLocations e hF hinv hep
  refine ⟨e, r, hr, he0, hsub, hinv, fun z hz => (he z hz).1, ?_⟩
  intro u hu v hv
  rw [hmetric u hu v hv, standardCone_zero_distance,
    ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm']

theorem flat_chart_geodesic_affine_parameter {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) {s u : ℝ} (hsu : s < u) (γ : ℝ → ℂ) (L : ℝ)
    (hsource : ∀ t ∈ Icc s u, γ t ∈ e.source)
    (hmetric : ∀ t ∈ Icc s u, ∀ v ∈ Icc s u,
      (pointSmoothConformalEDist a y (γ t) (γ v)).toReal = dist (e (γ t)) (e (γ v)))
    (hgeo : ∀ t ∈ Icc s u, ∀ v ∈ Icc s u,
      (pointSmoothConformalEDist a y (γ t) (γ v)).toReal = |v - t| * L)
    {t : ℝ} (ht : t ∈ Icc s u) :
    e (γ t) = AffineMap.lineMap (e (γ s)) (e (γ u)) ((t - s) / (u - s)) ∧
      γ t = e.symm (AffineMap.lineMap (e (γ s)) (e (γ u)) ((t - s) / (u - s))) := by
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
  have hu : u ∈ Icc s u := ⟨hsu.le, le_rfl⟩
  have hne : u - s ≠ 0 := sub_ne_zero.mpr hsu.ne'
  have hdist (v : ℝ) (hv : v ∈ Icc s u) (w : ℝ) (hw : w ∈ Icc s u) :
      dist (e (γ v)) (e (γ w)) = |w - v| * L :=
    (hmetric v hv w hw).symm.trans (hgeo v hv w hw)
  have heq : e (γ t) = AffineMap.lineMap (e (γ s)) (e (γ u)) ((t - s) / (u - s)) := by
    apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
    · rw [hdist s hs t ht, hdist s hs u hu,
        abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hsu.le)]
      field_simp
    · rw [hdist t ht u hu, hdist s hs u hu,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg (sub_nonneg.mpr hsu.le)]
      field_simp
      ring
  refine ⟨heq, ?_⟩
  rw [← heq, e.left_inv (hsource t ht)]

theorem flat_chart_geodesic_analytic {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) {s u : ℝ} (hsu : s < u) (γ : ℝ → ℂ) (L : ℝ)
    (hsource : ∀ t ∈ Icc s u, γ t ∈ e.source)
    (hinv : AnalyticOnNhd ℂ e.symm e.target)
    (hmetric : ∀ t ∈ Icc s u, ∀ v ∈ Icc s u,
      (pointSmoothConformalEDist a y (γ t) (γ v)).toReal = dist (e (γ t)) (e (γ v)))
    (hgeo : ∀ t ∈ Icc s u, ∀ v ∈ Icc s u,
      (pointSmoothConformalEDist a y (γ t) (γ v)).toReal = |v - t| * L) :
    AnalyticOnNhd ℝ γ (Ioo s u) := by
  intro t ht
  let l : ℝ → ℂ := fun v => AffineMap.lineMap (e (γ s)) (e (γ u)) ((v - s) / (u - s))
  have hl : AnalyticAt ℝ l t := by
    simp only [l, AffineMap.lineMap_apply_module']
    exact ((analyticAt_id.sub analyticAt_const).div_const.smul analyticAt_const).add analyticAt_const
  have heq (v : ℝ) (hv : v ∈ Icc s u) :=
    flat_chart_geodesic_affine_parameter a y e hsu γ L hsource hmetric hgeo hv
  have hlt : l t ∈ e.target := by
    dsimp [l]
    rw [← (heq t ⟨ht.1.le, ht.2.le⟩).1]
    exact e.mapsTo (hsource t ⟨ht.1.le, ht.2.le⟩)
  have hAi : AnalyticAt ℝ e.symm (l t) := (hinv _ hlt).restrictScalars
  apply (hAi.comp hl).congr
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
  exact (heq v ⟨hv.1.le, hv.2.le⟩).2.symm

end RepulsiveCoulomb
