module

public import LeanResearch.RepulsiveCoulomb.PointSectorReturnOrientedPoint
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnBothEndpointAngles

@[expose] public section

/-! Isolated, uncompiled actual frontend. The old boundary clock, actual Jordan
cap, clean-ray carrier avoidance, all three radial germs, endpoint labeling,
actual chart rotations, and full initial cap angle are constructed from the
original metric edge and clean boundary ray. No cap/side/angle certificate is
an input. The raw interior-direction hypothesis is on the already constructed
actual initial direction of the original metric edge. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

 theorem sectorReturn_actual_edge_finish_not_on_clean_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (E : PointGeodesicTreeEdge a y) (ρ : ℝ → ℂ)
    (hρ0 : ρ 0 = E.start)
    (hρd : ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v)
    (hρfront : ∀ u ∈ Ici (0 : ℝ), ρ u ∈ frontier P)
    (hgap : ∀ u : unitInterval, 0 < u.1 → u.1 < 1 → E.curve u ∉ frontier P) :
    ∀ T ∈ Ici (0 : ℝ), E.finish ≠ ρ T := by
  let F : PointClosedBoundaryGeodesicPiece a y :=
    { interval := Ici 0
      interval_closed := isClosed_Ici
      interval_convex := convex_Ici 0
      curve := fun u => ρ u
      metric := by
        intro u v
        change (pointSmoothConformalEDist a y (ρ (u : ℝ)) (ρ (v : ℝ))).toReal =
          dist (u : ℝ) (v : ℝ)
        exact hρd u u.2 v v.2 }
  intro T hT he
  obtain ⟨η, hη0, hη1, _, hηF, hηd⟩ := F.geodesicallyConvex ha y E.start
    ⟨⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩, hρ0⟩ E.finish ⟨⟨T, hT⟩, he.symm⟩
  have hsame : E.curve = η := pointConformal_geodesic_unique ha y E.start E.finish
    E.curve η E.curve_start E.curve_finish hη0 hη1 E.geodesic hηd
  let u : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hbound : E.curve u ∈ frontier P := by
    rw [hsame]
    obtain ⟨v, hv⟩ := hηF u
    rw [← hv]
    exact hρfront v v.2
  exact hgap u (by norm_num [u]) (by norm_num [u]) hbound

/-- The full actual initial-angle frontend for a hypothetical sector return.
The cap and its retained chart are OUTPUTS. Both old-boundary clock and full
retained-link orientations are resolved inside the proof. -/
theorem exists_sectorReturn_actual_cap_initial_angle
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (E : PointGeodesicTreeEdge a y) (hEP : ∀ u, E.curve u ∈ P)
    (C : PointRetainedConeNeighborhood a y P E.start) (hadm : C.Admissible)
    (hφopen : C.actualInitialRawAngle ha y hadm E rfl hEP ∈ Ioo C.lo C.hi)
    (ρ : ℝ → ℂ) (hρ : Continuous ρ) (hρ0 : ρ 0 = E.start)
    (hρd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρfront : ∀ t ∈ Ici (0 : ℝ), ρ t ∈ frontier P)
    (hgap : ∀ u : unitInterval, 0 < u.1 → u.1 < 1 → E.curve u ∉ frontier P)
    (hfinish : E.finish ∈ frontier P) :
    ∃ b : ℝ → ℂ, Continuous b ∧ Function.Injective b ∧ range b = frontier P ∧
      ∃ s t : ℝ, s < t ∧ b s = E.start ∧ b t = E.finish ∧
        let K := range E.curve ∪ range (lineCapSegment b s t)
        Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' K) ∧
        ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
          Disjoint U V ∧ U ∪ V = Kᶜ ∧ frontier U = K ∧ frontier V = K ∧
          IsCompact (closure U) ∧ closure U ⊆ P ∧
          ∃ ξ : ℝ, ξ ∈ Icc C.lo C.hi ∧ (ξ = C.lo ∨ ξ = C.hi) ∧
            ∃ ε : ℝ, 0 < ε ∧
              (∀ u ∈ Ioo (0 : ℝ) ε, C.chart (ρ u) = pointRadialSectorPoint u ξ) ∧
            ∃ D : PointRetainedConeNeighborhood a y (closure U) E.start,
              (1 + coalescedPointExponent a y E.start / 2) * (D.hi - D.lo) =
                (1 + coalescedPointExponent a y E.start / 2) * (C.hi - C.lo) -
                  (1 + coalescedPointExponent a y E.start / 2) *
                    |C.actualInitialRawAngle ha y hadm E rfl hEP - ξ| ∧
              Real.pi - (1 + coalescedPointExponent a y E.start / 2) * (D.hi - D.lo) =
                (Real.pi - (1 + coalescedPointExponent a y E.start / 2) * (C.hi - C.lo)) +
                  (1 + coalescedPointExponent a y E.start / 2) *
                    |C.actualInitialRawAngle ha y hadm E rfl hEP - ξ| := by
  have hq := sectorReturn_actual_edge_finish_not_on_clean_ray ha y E ρ hρ0 hρd hρfront hgap
  obtain ⟨b, hb, hbi, hboundary, s, t, hst, hs, ht, hρlower⟩ :=
    exists_clean_ray_oriented_boundary_to_external_point ha y H hP ρ hρd hρfront hfinish hq
  have hsE : b s = E.start := hs.trans hρ0
  let r := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) E.curve
  have hr : Continuous r := continuous_IccExtend_iff.mpr E.continuous
  have hrval (u : unitInterval) : r u = E.curve u := IccExtend_val _ _ u
  have hr0 : r 0 = E.start := (hrval 0).trans E.curve_start
  have hr1 : r 1 = E.finish := (hrval 1).trans E.curve_finish
  have hα : lineCapSegment r 0 1 = E.curve := by
    funext u
    simpa only [lineCapSegment, sub_zero, mul_one, zero_add] using hrval u
  have hiE : Function.Injective E.curve :=
    pointConformal_geodesic_injective ha y E.distinct E.curve E.geodesic
  have hri : InjOn r (Icc (0 : ℝ) 1) := by
    intro u hu v hv he
    have he' : E.curve ⟨u, hu⟩ = E.curve ⟨v, hv⟩ := by
      rw [← hrval, ← hrval]
      exact he
    exact congrArg Subtype.val (hiE he')
  have hgapR : ∀ u ∈ Ioo (0 : ℝ) 1, r u ∉ frontier P := by
    intro u hu
    have h := hgap ⟨u, ⟨hu.1.le, hu.2.le⟩⟩ hu.1 hu.2
    rwa [← hrval] at h
  have hrP : MapsTo r (Icc (0 : ℝ) 1) P := by
    intro u hu
    have h := hEP ⟨u, hu⟩
    rwa [← hrval] at h
  have hstart : r 0 ∈ frontier P := by rw [hr0, ← hρ0]; exact hρfront 0 (show (0 : ℝ) ≤ 0 from le_rfl)
  have hend : r 1 ∈ frontier P := by rwa [hr1]
  obtain ⟨s', t', hs', ht', _, hJ, U, V, hU, hV, hUc, hVc, hUV,
      hcover, hfrontU, hfrontV, hcompact, hUP⟩ := exists_firstReturn_actual_cap H hP b r
    hb hbi hboundary hr (by norm_num : (0 : ℝ) < 1) hri hstart hend hrP hgapR
  have hss : s' = s := hbi (hs'.trans (hr0.trans hsE.symm))
  have htt : t' = t := hbi (ht'.trans (hr1.trans ht.symm))
  subst s'
  subst t'
  rw [hα] at hJ hcover hfrontU hfrontV
  let β := lineCapSegment b s t
  have hβ : Continuous β := lineCapSegment_continuous hb s t
  have hiβ : Function.Injective β := lineCapSegment_injective_of_ne hbi hst.ne
  have hβ0 : β 0 = E.start := (lineCapSegment_zero b s t).trans hsE
  have hβfront (u : unitInterval) : β u ∈ frontier P := by
    rw [← hboundary]
    exact ⟨s + u.1 * (t - s), rfl⟩
  have havoid : ∀ u : ℝ, 0 < u → ρ u ∉ range E.curve ∪ range β := by
    have h := firstReturn_clean_old_end_avoids_carrier hbi hboundary
      (by norm_num : (0 : ℝ) < 1) hst (hsE.trans hr0.symm) (ht.trans hr1.symm) hgapR hρlower
    simpa only [hα] using h
  have hclosed : IsClosed P := by
    have h := (straightened_halfplane_complement_geometry H).1
    rwa [← hP] at h
  obtain ⟨ξ, hξ, hξend, ε, hε, hξgerm, D, hD⟩ := exists_sectorReturn_actual_both_endpoint_cap_angle
    ha y C hclosed hadm E rfl hEP hφopen β hβ hiβ hβ0 hβfront
    ρ hρ hρ0 hρd hρfront havoid hU hV hUV hcover hcompact hfrontU hfrontV
  exact ⟨b, hb, hbi, hboundary, s, t, hst, hsE, ht, hJ, U, V,
    hU, hV, hUc, hVc, hUV, hcover, hfrontU, hfrontV, hcompact, hUP,
    ξ, hξ, hξend, ε, hε, hξgerm, D, hD, by linarith⟩

end RepulsiveCoulomb
