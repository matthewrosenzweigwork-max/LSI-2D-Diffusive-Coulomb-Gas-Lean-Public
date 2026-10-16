import LeanResearch.RepulsiveCoulomb.PointActualMarkedDirection

/-! ISOLATED SOURCE-ONLY exact subsegment consistency. The curves compared here
are the actual minimizing segments and literal clean-ray restrictions. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Affine source clocks of initial restrictions multiply associatively. -/
theorem pointEdgeSubparam_zero_assoc (s t u : unitInterval) :
    pointEdgeSubparam 0 s (pointEdgeSubparam 0 t u) =
      pointEdgeSubparam 0 (pointEdgeSubparam 0 s t) u := by
  apply Subtype.ext
  simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module',
    Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
  ring

/-- The constructed full raw direction is unchanged on any actual initial
restriction. This proves consistency of the selector rather than assuming it. -/
theorem PointRetainedConeNeighborhood.actualInitialRawAngle_of_prefix
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E G : PointGeodesicTreeEdge a y)
    (hE0 : E.start = p) (hG0 : G.start = p)
    (hEP : ∀ t, E.curve t ∈ P) (hGP : ∀ t, G.curve t ∈ P)
    {t : unitInterval} (ht : 0 < t.1)
    (hcurve : G.curve = E.curve ∘ pointEdgeSubparam 0 t) :
    C.actualInitialRawAngle ha y hadm G hG0 hGP =
      C.actualInitialRawAngle ha y hadm E hE0 hEP := by
  obtain ⟨hθ, r, τ, hr, _, hτ, _, hradG⟩ :=
    C.actualInitialRawAngle_spec ha y hadm G hG0 hGP
  obtain ⟨hφ, s, σ, hs, _, hσ, _, hradE⟩ :=
    C.actualInitialRawAngle_spec ha y hadm E hE0 hEP
  let v := pointEdgeSubparam 0 t τ
  have hv : 0 < v.1 := by
    change 0 < (AffineMap.lineMap (0 : ℝ) t.1 τ.1)
    simpa [AffineMap.lineMap_apply_module', smul_eq_mul] using mul_pos hτ ht
  have htransport (u : unitInterval) :
      C.chart (E.curve (pointEdgeSubparam 0 v u)) =
        pointRadialSectorPoint (u.1 * r)
          (C.actualInitialRawAngle ha y hadm G hG0 hGP) := by
    have h := hradG u
    rw [hcurve] at h
    simpa only [Function.comp_apply, pointEdgeSubparam_zero_assoc] using h
  exact C.actual_initial_raw_angle_unique hadm E
    hr hs hv hσ hθ hφ htransport hradE

/-- Endpoint uniqueness identifies the chosen segment to a point on an edge
with its actual normalized prefix. No independently chosen continuation is used. -/
theorem pointActualEdge_curve_of_endpoint_on_edge
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (E G : PointGeodesicTreeEdge a y) (hstart : G.start = E.start)
    {t : unitInterval} (ht : 0 < t.1) (hfinish : G.finish = E.curve t) :
    G.curve = E.curve ∘ pointEdgeSubparam 0 t := by
  let D := pointGeodesicSubedge ha y E 0 t ht
  have hD0 : D.start = G.start := by
    change E.curve 0 = G.start
    exact E.curve_start.trans hstart.symm
  have hD1 : D.finish = G.finish := hfinish.symm
  have hDgeo := D.geodesic
  rw [hD0, hD1] at hDgeo
  exact pointConformal_geodesic_unique ha y G.start G.finish G.curve D.curve
    G.curve_start G.curve_finish (D.curve_start.trans hD0)
    (D.curve_finish.trans hD1) G.geodesic hDgeo

/-- The actual endpoint metric fixes the prefix speed exactly. -/
theorem pointActualEdgeLength_of_endpoint_on_edge
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (E G : PointGeodesicTreeEdge a y) (hstart : G.start = E.start)
    (t : unitInterval) (hfinish : G.finish = E.curve t) :
    pointActualEdgeLength G = t.1 * pointActualEdgeLength E := by
  calc
    pointActualEdgeLength G =
        (pointSmoothConformalEDist a y E.start (E.curve t)).toReal := by
      rw [pointActualEdgeLength, hstart, hfinish]
    _ = t.1 * pointActualEdgeLength E := by
      have h := E.geodesic 0 t
      have hE0 : E.curve (0 : unitInterval) = E.start := E.curve_start
      rw [hE0, Set.Icc.coe_zero, sub_zero, abs_of_nonneg t.2.1] at h
      exact h

/-- Equal physical times identify the two literal comparison-ray prefixes. -/
theorem pointRayComparisonEdge_curve_of_length_mul
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (E G : PointGeodesicTreeEdge a y) (t : unitInterval)
    (hlen : pointActualEdgeLength G = t.1 * pointActualEdgeLength E) :
    (pointRayComparisonEdge ha y ρ hρ G).curve =
      (pointRayComparisonEdge ha y ρ hρ E).curve ∘ pointEdgeSubparam 0 t := by
  funext u
  simp only [Function.comp_apply, pointRayComparisonEdge_curve]
  apply congrArg ρ
  apply Subtype.ext
  simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module',
    Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
  rw [hlen]
  ring

/-- The full physical initial direction from the SAME actual clean ray is
unchanged on a chosen actual endpoint subsegment. Both the endpoint segment and
the comparison-ray segment are identified by their actual source clocks. -/
theorem PointRetainedConeNeighborhood.actualPhysicalDirection_of_endpoint_on_edge
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    (E G : PointGeodesicTreeEdge a y)
    (hE0 : E.start = ρ 0) (hG0 : G.start = ρ 0)
    (hEP : ∀ t, E.curve t ∈ P) (hGP : ∀ t, G.curve t ∈ P)
    {t : unitInterval} (ht : 0 < t.1) (hfinish : G.finish = E.curve t) :
    C.actualPhysicalDirection ha y hadm G (pointRayComparisonEdge ha y ρ hρ G)
      hG0 rfl hGP (fun u ↦ hρP _) =
    C.actualPhysicalDirection ha y hadm E (pointRayComparisonEdge ha y ρ hρ E)
      hE0 rfl hEP (fun u ↦ hρP _) := by
  have hstart : G.start = E.start := hG0.trans hE0.symm
  have hcurve := pointActualEdge_curve_of_endpoint_on_edge ha y E G hstart ht hfinish
  have hangle := C.actualInitialRawAngle_of_prefix ha y hadm E G hE0 hG0 hEP hGP ht hcurve
  have hlen := pointActualEdgeLength_of_endpoint_on_edge E G hstart t hfinish
  have hraycurve := pointRayComparisonEdge_curve_of_length_mul ha y ρ hρ E G t hlen
  have hrayangle := C.actualInitialRawAngle_of_prefix ha y hadm
    (pointRayComparisonEdge ha y ρ hρ E) (pointRayComparisonEdge ha y ρ hρ G)
    rfl rfl (fun u ↦ hρP _) (fun u ↦ hρP _) ht hraycurve
  unfold actualPhysicalDirection
  rw [hangle, hrayangle]

/-- Every positive literal prefix of the SAME actual metric ray has the same
full raw initial germ. Consequently the marked-point-dependent comparison
length does not change the endpoint used to anchor the physical interval. -/
theorem PointRetainedConeNeighborhood.comparisonRay_initial_angle_independent
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    (E G : PointGeodesicTreeEdge a y) :
    C.actualInitialRawAngle ha y hadm (pointRayComparisonEdge ha y ρ hρ E)
      rfl (fun u ↦ hρP _) =
    C.actualInitialRawAngle ha y hadm (pointRayComparisonEdge ha y ρ hρ G)
      rfl (fun u ↦ hρP _) := by
  have ordered (A B : PointGeodesicTreeEdge a y)
      (hAB : pointActualEdgeLength A ≤ pointActualEdgeLength B) :
      C.actualInitialRawAngle ha y hadm (pointRayComparisonEdge ha y ρ hρ A)
        rfl (fun u ↦ hρP _) =
      C.actualInitialRawAngle ha y hadm (pointRayComparisonEdge ha y ρ hρ B)
        rfl (fun u ↦ hρP _) := by
    have hA := pointActualEdgeLength_pos ha y A
    have hB := pointActualEdgeLength_pos ha y B
    let t : unitInterval := ⟨pointActualEdgeLength A / pointActualEdgeLength B,
      (div_pos hA hB).le, (div_le_one hB).mpr hAB⟩
    have ht : 0 < t.1 := div_pos hA hB
    have hlen : pointActualEdgeLength A = t.1 * pointActualEdgeLength B :=
      (div_mul_cancel₀ _ hB.ne').symm
    have hcurve := pointRayComparisonEdge_curve_of_length_mul ha y ρ hρ B A t hlen
    exact C.actualInitialRawAngle_of_prefix ha y hadm
      (pointRayComparisonEdge ha y ρ hρ B) (pointRayComparisonEdge ha y ρ hρ A)
      rfl rfl (fun u ↦ hρP _) (fun u ↦ hρP _) ht hcurve
  rcases le_total (pointActualEdgeLength E) (pointActualEdgeLength G) with h | h
  · exact ordered E G h
  · exact (ordered G E h).symm

end RepulsiveCoulomb
