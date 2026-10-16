import LeanResearch.RepulsiveCoulomb.PointClassicalConeChart

/-! Full closed-disk local isometries to classical cones, including onto-ness.
The model disk uses ordinary modulus as its intrinsic radius. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointClassicalConeDist_apex {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p w : ℂ) :
    pointClassicalConeDist a y p w 0 = ‖w‖ := classicalCone_dist_apex _ _ _

theorem exists_pointConformal_classical_cone_disk {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ, 0 < r ∧ e p = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ r} ⊆ e.source ∧
      Set.BijOn e {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ r} {w : ℂ | ‖w‖ ≤ r} ∧
      ∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ r →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ r →
          (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (e u) (e v) := by
  obtain ⟨e, hp, h0, hd⟩ := exists_pointConformal_classical_chart ha y p
  let S := pointSmoothConformalMetricSpace ha y
  let T := pointClassicalConeMetricSpace a y p
  have hS := pointSmoothConformalMetricSpace_topology ha y
  have hT := pointClassicalConeMetricSpace_topology a y p
  let eM := retopologizeOpenPartialHomeomorph e S.toUniformSpace.toTopologicalSpace
    T.toUniformSpace.toTopologicalSpace hS hT
  have he := retopologizeOpenPartialHomeomorph_toPartialEquiv e
    S.toUniformSpace.toTopologicalSpace T.toUniformSpace.toTopologicalSpace hS hT
  have hf : (eM : ℂ → ℂ) = e := congrArg PartialEquiv.toFun he
  have hs : eM.source = e.source := congrArg PartialEquiv.source he
  have hpres : ∀ u ∈ eM.source, ∀ v ∈ eM.source,
      @dist ℂ T.toDist (eM u) (eM v) = @dist ℂ S.toDist u v := by
    intro u hu v hv
    rw [hs] at hu hv
    change pointClassicalConeDist a y p (eM u) (eM v) = (pointSmoothConformalEDist a y u v).toReal
    rw [hf]
    exact (hd u hu v hv).symm
  obtain ⟨r, hr, hball, hbij⟩ := @exists_closedBall_bijOn_of_local_chart ℂ ℂ S T eM p
    (by rw [hs]; exact hp) hpres
  change {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ r} ⊆ eM.source at hball
  rw [hs] at hball
  change Set.BijOn (eM : ℂ → ℂ) {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ r}
    {w : ℂ | pointClassicalConeDist a y p w (eM p) ≤ r} at hbij
  rw [hf, h0] at hbij
  simp_rw [pointClassicalConeDist_apex] at hbij
  exact ⟨e, r, hr, h0, hball, hbij, fun u hu v hv ↦ hd u (hball hu) v (hball hv)⟩

end RepulsiveCoulomb
