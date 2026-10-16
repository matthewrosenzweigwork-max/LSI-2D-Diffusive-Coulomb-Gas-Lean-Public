import LeanResearch.RepulsiveCoulomb.PointFlatGeodesicParametrization

/-! Actual real-analytic regularity of constant-speed point-conformal geodesics
at every interior parameter away from positive-exponent punctures. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointConformal_geodesic_analyticAt {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y) :
    AnalyticAt ℝ γ t := by
  obtain ⟨e, r, hr, _, hsource, hinv, _, hmetric⟩ :=
    exists_pointConformal_flat_analytic_metric_chart ha y hp
  let U : Set ℝ := Ioo 0 1 ∩ γ ⁻¹' ball (γ t) r
  have hU : IsOpen U := isOpen_Ioo.inter (isOpen_ball.preimage hc)
  have htU : t ∈ U := ⟨ht, mem_ball_self hr⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU t htU
  have hlocal : ∀ v ∈ Icc (t - ε / 2) (t + ε / 2), v ∈ U := by
    intro v hv
    apply hsub
    rw [mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hinterval (v : ℝ) (hv : v ∈ Icc (t - ε / 2) (t + ε / 2)) : v ∈ Icc (0 : ℝ) 1 :=
    ⟨(hlocal v hv).1.1.le, (hlocal v hv).1.2.le⟩
  have hA := flat_chart_geodesic_analytic a y e
    (show t - ε / 2 < t + ε / 2 by linarith) γ L
    (fun v hv => hsource (hlocal v hv).2) hinv
    (fun v hv w hw => hmetric _ (hlocal v hv).2 _ (hlocal w hw).2)
    (fun v hv w hw => hgeo v (hinterval v hv) w (hinterval w hw))
  exact hA t ⟨by linarith, by linarith⟩

theorem pointConformal_geodesic_extension_analyticAt {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ}
    (γ : Icc (0 : ℝ) 1 → ℂ) (hc : Continuous γ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hp : γ ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ ∉ pointPunctures a y) :
    AnalyticAt ℝ (IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ) t := by
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  have hg : Continuous g := continuous_IccExtend_iff.mpr hc
  apply pointConformal_geodesic_analyticAt ha y g hg
    (pointSmoothConformalEDist a y x z).toReal ?_ ht ?_
  · intro s hs u hu
    dsimp [g]
    rw [IccExtend_of_mem _ _ hs, IccExtend_of_mem _ _ hu]
    exact hd ⟨s, hs⟩ ⟨u, hu⟩
  · simpa only [g, IccExtend_of_mem _ _ ⟨ht.1.le, ht.2.le⟩] using hp

end RepulsiveCoulomb
