module

public import LeanResearch.RepulsiveCoulomb.PointConformalPathTransport

@[expose] public section

/-! From exact local curve-length transport to an actual local equality of the
ambient smooth-path metrics. Short competitors are proved to stay in the chart;
this rules out hidden shortcuts through its complement. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem exists_real_pointConformal_ball_subset {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {U : Set ℂ} (hU : IsOpen U) {p : ℂ} (hp : p ∈ U) :
    ∃ R : ℝ, 0 < R ∧ ∀ z, pointSmoothConformalEDist a y p z < ENNReal.ofReal R → z ∈ U := by
  obtain ⟨r, hr, hsub⟩ := pointConformal_ball_subset_open ha y hU hp
  obtain ⟨R, _, hR, hRr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hr
  exact ⟨R, ENNReal.ofReal_pos.mp hR, fun z hz ↦ hsub z (hz.trans hRr)⟩

theorem pointConformal_local_distance_comparison {m n : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (b : Fin n → ℝ) (w : Fin n → ℂ)
    {U : Set ℂ} {F : ℂ → ℂ} {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : ∀ z, pointSmoothConformalEDist a y p z < ENNReal.ofReal R → z ∈ U)
    (H : ∀ γ : ℝ → ℂ, ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) U →
      ContDiffOn ℝ 1 (F ∘ γ) (Icc (0 : ℝ) 1) ∧
      pointConformalPathELength a y γ 0 1 = pointConformalPathELength b w (F ∘ γ) 0 1)
    {u v : ℂ} (hu : pointSmoothConformalEDist a y p u ≤ ENNReal.ofReal (R / 8))
    (hv : pointSmoothConformalEDist a y p v ≤ ENNReal.ofReal (R / 8)) :
    pointSmoothConformalEDist b w (F u) (F v) ≤ pointSmoothConformalEDist a y u v := by
  have hsmall : pointSmoothConformalEDist a y u v < ENNReal.ofReal (R / 2) := by
    calc
      _ ≤ pointSmoothConformalEDist a y u p + pointSmoothConformalEDist a y p v :=
        pointSmoothConformalEDist_triangle a y _ _ _
      _ = pointSmoothConformalEDist a y p u + pointSmoothConformalEDist a y p v := by
        rw [pointSmoothConformalEDist_comm a y u p]
      _ ≤ ENNReal.ofReal (R / 8) + ENNReal.ofReal (R / 8) := add_le_add hu hv
      _ < ENNReal.ofReal (R / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < R / 2)]
        linarith
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y (lt_min hr hsmall)
  have hlenR : pointConformalPathELength a y γ 0 1 ≤ ENNReal.ofReal (R / 2) :=
    hlen.le.trans (min_le_right _ _)
  have hstart : pointSmoothConformalEDist a y p (γ 0) ≤ ENNReal.ofReal (R / 4) := by
    rw [h0]
    exact hu.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) U := fun t ht ↦
    hsub _ (pointConformal_path_localization a y hγ.contDiffOn hR hstart hlenR t ht)
  have hT := H γ hγ.contDiffOn hmap
  have hd := pointSmoothConformalEDist_le_path b w hT.1 zero_le_one
  change pointSmoothConformalEDist b w (F (γ 0)) (F (γ 1)) ≤ _ at hd
  rw [h0, h1, ← hT.2] at hd
  exact (hd.trans_lt hlen).trans_le (min_le_left _ _)

/-- Actual local isometry of ambient metrics induced by a biholomorphic density chart. -/
theorem pointConformal_chart_local_metric_eq {m n : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {b : Fin n → ℝ}
    (hb : ∀ j, 0 ≤ b j) (w : Fin n → ℂ) (e : OpenPartialHomeomorph ℂ ℂ)
    (hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity b w (e z) * ‖deriv e z‖ = pointConformalDensity a y z)
    (hInv : AnalyticOnNhd ℂ e.symm e.target) {p : ℂ} (hp : p ∈ e.source) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ e.source ∧ ∀ u ∈ ball p r, ∀ v ∈ ball p r,
      pointSmoothConformalEDist a y u v = pointSmoothConformalEDist b w (e u) (e v) := by
  obtain ⟨Rs, hRs, hsball⟩ := exists_real_pointConformal_ball_subset ha y e.open_source hp
  obtain ⟨Rt, hRt, htball⟩ := exists_real_pointConformal_ball_subset hb w e.open_target (e.map_source hp)
  have hse : ∀ᶠ z in 𝓝 p, pointSmoothConformalEDist a y p z < ENNReal.ofReal (Rs / 8) :=
    (pointSmoothConformalEDist_tendsto_zero ha y p).eventually
      (eventually_lt_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  have hte : ∀ᶠ z in 𝓝 p, pointSmoothConformalEDist b w (e p) (e z) < ENNReal.ofReal (Rt / 8) :=
    ((pointSmoothConformalEDist_tendsto_zero hb w (e p)).comp (e.continuousAt hp).tendsto).eventually
      (eventually_lt_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
  have hboth : {z | z ∈ e.source ∧ pointSmoothConformalEDist a y p z ≤ ENNReal.ofReal (Rs / 8) ∧
      pointSmoothConformalEDist b w (e p) (e z) ≤ ENNReal.ofReal (Rt / 8)} ∈ 𝓝 p := by
    filter_upwards [e.open_source.mem_nhds hp, hse, hte] with z hz hs ht
    exact ⟨hz, hs.le, ht.le⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hboth
  refine ⟨r, hr, fun z hz ↦ (hsub hz).1, ?_⟩
  intro u hu v hv
  have hfwd := pointConformal_local_distance_comparison a y b w hRs hsball
    (F := (e : ℂ → ℂ)) (fun γ hγ hm ↦
      ⟨analyticOnNhd_comp_smooth_path (fun z hz ↦ (hF z hz).1) hγ hm,
        pointConformalPath_transport a y b w hF hγ hm⟩) (hsub hu).2.1 (hsub hv).2.1
  have hbwd := pointConformal_local_distance_comparison b w a y hRt htball
    (F := (e.symm : ℂ → ℂ)) (fun η hη hm ↦
      ⟨analyticOnNhd_comp_smooth_path hInv hη hm,
        (pointConformalPath_transport_inverse a y b w e hF hInv hη hm).symm⟩)
    (hsub hu).2.2 (hsub hv).2.2
  rw [e.left_inv (hsub hu).1, e.left_inv (hsub hv).1] at hbwd
  exact le_antisymm hbwd hfwd

end RepulsiveCoulomb
