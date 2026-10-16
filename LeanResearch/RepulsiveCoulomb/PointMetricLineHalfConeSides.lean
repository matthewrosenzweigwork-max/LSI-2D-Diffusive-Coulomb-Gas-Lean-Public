module

public import LeanResearch.RepulsiveCoulomb.PointMetricLineNormalizedChart
public import LeanResearch.RepulsiveCoulomb.PointClosedRegionIntrinsicMetric
public import LeanResearch.RepulsiveCoulomb.PointRadialChartSideTransport

@[expose] public section

/-! Identify the actual closed sides with the two actual local cone sectors.
The side assignment is obtained from the actual open-region partition, common
frontiers and the constructed whole-line boundary chart. No orientation or
half-cone side certificate is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Exact closed-side membership follows from a genuine local boundary
partition and the proved open-side assignments. -/
theorem chart_closed_side_membership {X : Type*} [TopologicalSpace X]
    {C U V : Set X} (hUV : Disjoint U V) (hcover : U ∪ V = Cᶜ)
    (hfront : frontier U = C) (e : OpenPartialHomeomorph X ℂ)
    {D B S T : Set ℂ} (hboundary : ∀ z ∈ D, e.symm z ∈ C ↔ z ∈ B)
    (hpartition : D \ B = S ∪ T) (hS : MapsTo e.symm S U) (hT : MapsTo e.symm T V) :
    ∀ z ∈ D, e.symm z ∈ closure U ↔ z ∈ B ∪ S := by
  have hcl : closure U = U ∪ C := by rw [closure_eq_self_union_frontier, hfront]
  intro z hz
  constructor
  · intro hx
    rcases (hcl ▸ hx) with hU | hC
    · have hzB : z ∉ B := by
        intro h
        have hx : e.symm z ∈ U ∪ V := Or.inl hU
        rw [hcover] at hx
        exact hx ((hboundary z hz).mpr h)
      have hST : z ∈ S ∪ T := hpartition ▸ And.intro hz hzB
      exact Or.inr (hST.resolve_right (fun h ↦ disjoint_left.mp hUV hU (hT h)))
    · exact Or.inl ((hboundary z hz).mp hC)
  · rintro (hzB | hzS)
    · rw [hcl]
      exact Or.inr ((hboundary z hz).mpr hzB)
    · exact subset_closure (hS hzS)

/-- Both local half-cones are identified as actual subsets of the same full
cone chart. Their induced metrics are the already constructed intrinsic side
metrics, since those equal the ambient point distance. -/
theorem exists_pointMetricLine_actual_halfcone_sides {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hℓ : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range ℓ)ᶜ ∧ frontier U = range ℓ ∧ frontier V = range ℓ ∧
      PointGeodesicallyConvex a y (closure U) ∧ PointGeodesicallyConvex a y (closure V) ∧
      ∃ F : OpenPartialHomeomorph ℂ ℂ, ∃ R θ : ℝ,
        0 < R ∧ 0 < θ ∧ θ < 2 * Real.pi ∧ ℓ 0 ∈ F.source ∧ F (ℓ 0) = 0 ∧
        ball (0 : ℂ) R ⊆ F.target ∧
        (∀ u, (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R →
          ∀ v, (pointSmoothConformalEDist a y v (ℓ 0)).toReal ≤ R →
            (pointSmoothConformalEDist a y u v).toReal =
              pointClassicalConeDist a y (ℓ 0) (F u) (F v)) ∧
        (∀ z ∈ ball (0 : ℂ) R,
          (F.symm z ∈ closure U ↔ z ∈
            (pointDiskRay R 0 ∪ pointDiskRay R θ) ∪ pointOpenRadialSector R 0 θ) ∧
          (F.symm z ∈ closure V ↔ z ∈
            (pointDiskRay R 0 ∪ pointDiskRay R θ) ∪ pointOpenRadialSector R θ (2 * Real.pi))) ∧
        Real.pi ≤ (coalescedPointExponent a y (ℓ 0) / 2 + 1) * θ ∧
        Real.pi ≤ (coalescedPointExponent a y (ℓ 0) / 2 + 1) * (2 * Real.pi - θ) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hUP, hVP⟩ :=
    exists_pointMetricLine_intrinsically_geodesic_sides ha y ℓ hℓ
  obtain ⟨F, R, θ, hR, hθ0, hθ2, hp, hF0, _, _, hmetric, htarget, hboundary, hθleft, hθright⟩ :=
    exists_pointMetricLine_normalized_chart ha y ℓ hℓ
  have hpU : ℓ 0 ∈ closure U := frontier_subset_closure (hfu.symm ▸ mem_range_self 0)
  have hpV : ℓ 0 ∈ closure V := frontier_subset_closure (hfv.symm ▸ mem_range_self 0)
  have hpartition := pointDiskRay_complement_eq_sectors hR hθ0 hθ2
  have hpartition' : ball (0 : ℂ) R \ (pointDiskRay R 0 ∪ pointDiskRay R θ) =
      pointOpenRadialSector R θ (2 * Real.pi) ∪ pointOpenRadialSector R 0 θ := by
    simpa only [union_comm] using hpartition
  rcases pointRadialChart_region_side_choice hU hV hUV hcover hpU hpV F hp hF0
    hR hθ0 hθ2 htarget hboundary with hside | hside
  · refine ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hUP, hVP,
      F, R, θ, hR, hθ0, hθ2, hp, hF0, htarget, hmetric, ?_, hθleft, hθright⟩
    intro z hz
    exact ⟨chart_closed_side_membership hUV hcover hfu F hboundary hpartition
        hside.1 hside.2 z hz,
      chart_closed_side_membership hUV.symm (by simpa only [union_comm] using hcover)
        hfv F hboundary hpartition' hside.2 hside.1 z hz⟩
  · refine ⟨V, U, hV, hU, hVc, hUc, hUV.symm, ?_, hfv, hfu, hVP, hUP,
      F, R, θ, hR, hθ0, hθ2, hp, hF0, htarget, hmetric, ?_, hθleft, hθright⟩
    · simpa only [union_comm] using hcover
    · intro z hz
      exact ⟨chart_closed_side_membership hUV.symm (by simpa only [union_comm] using hcover)
          hfv F hboundary hpartition hside.1 hside.2 z hz,
        chart_closed_side_membership hUV hcover hfu F hboundary hpartition'
          hside.2 hside.1 z hz⟩

end RepulsiveCoulomb
