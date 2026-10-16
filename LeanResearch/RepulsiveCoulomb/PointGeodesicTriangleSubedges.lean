import LeanResearch.RepulsiveCoulomb.GeodesicTriangleBridgeInterval

/-! Three actual nondegenerate minimizing subedges forming a simple triangle
are extracted from two disjoint minimizing legs and a shorter shortcut. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem geodesic_subedge_range_subset {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) :
    range (pointGeodesicSubedge ha y E s t hst).curve ⊆ range E.curve := by
  rw [pointGeodesicSubedge_range]
  rintro z ⟨u, hu, rfl⟩
  exact mem_range_self u

structure PointSimpleGeodesicTriangle {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (q : ℂ) where
  left : PointGeodesicTreeEdge a y
  right : PointGeodesicTreeEdge a y
  cross : PointGeodesicTreeEdge a y
  left_start : left.start = q
  right_start : right.start = q
  cross_start : cross.start = left.finish
  cross_finish : cross.finish = right.finish
  legs_meet : range left.curve ∩ range right.curve = {q}
  cross_left : range cross.curve ∩ range left.curve = {cross.start}
  cross_right : range cross.curve ∩ range right.curve = {cross.finish}

/-- This triangle uses only restrictions of the supplied minimizing legs and
shortcut. Pairwise singleton intersections are conclusions of the construction. -/
theorem exists_pointGeodesic_simple_triangle_subedges {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (A B γ : PointGeodesicTreeEdge a y) (q : ℂ)
    (hA : A.start = q) (hB : B.start = q)
    (hγA : γ.start = A.finish) (hγB : γ.finish = B.finish)
    (hmeet : range A.curve ∩ range B.curve = {q})
    (hshort : (pointSmoothConformalEDist a y γ.start γ.finish).toReal <
      (pointSmoothConformalEDist a y γ.start q).toReal +
        (pointSmoothConformalEDist a y q γ.finish).toReal) :
    ∃ T : PointSimpleGeodesicTriangle a y q,
      range T.left.curve ⊆ range A.curve ∧ range T.right.curve ⊆ range B.curve ∧
        range T.cross.curve ⊆ range γ.curve := by
  obtain ⟨s, t, hst, hsA, htB, hsmeet, htmeet, hsne, htne⟩ :=
    exists_pointGeodesic_shortcut_bridge ha y A B γ q hA hB hγA hγB hmeet hshort
  obtain ⟨u, hu⟩ := hsA
  obtain ⟨v, hv⟩ := htB
  have hu0 : 0 < u.1 := by
    apply lt_of_le_of_ne u.2.1
    intro he
    apply hsne
    have hu' : u = ⟨0, by norm_num⟩ := Subtype.ext he.symm
    rw [← hu, hu', A.curve_start, hA]
  have hv0 : 0 < v.1 := by
    apply lt_of_le_of_ne v.2.1
    intro he
    apply htne
    have hv' : v = ⟨0, by norm_num⟩ := Subtype.ext he.symm
    rw [← hv, hv', B.curve_start, hB]
  let A' := pointGeodesicSubedge ha y A ⟨0, by norm_num⟩ u hu0
  let B' := pointGeodesicSubedge ha y B ⟨0, by norm_num⟩ v hv0
  let C' := pointGeodesicSubedge ha y γ s t hst
  have hA's : A'.start = q := A.curve_start.trans hA
  have hB's : B'.start = q := B.curve_start.trans hB
  have hC's : C'.start = A'.finish := hu.symm
  have hC'f : C'.finish = B'.finish := hv.symm
  have hA'sub := geodesic_subedge_range_subset ha y A ⟨0, by norm_num⟩ u hu0
  have hB'sub := geodesic_subedge_range_subset ha y B ⟨0, by norm_num⟩ v hv0
  have hC'sub := geodesic_subedge_range_subset ha y γ s t hst
  have hA'q : q ∈ range A'.curve := ⟨⟨0, by norm_num⟩, A'.curve_start.trans hA's⟩
  have hB'q : q ∈ range B'.curve := ⟨⟨0, by norm_num⟩, B'.curve_start.trans hB's⟩
  have hlegs : range A'.curve ∩ range B'.curve = {q} := by
    apply Subset.antisymm
    · intro z hz
      rw [← hmeet]
      exact ⟨hA'sub hz.1, hB'sub hz.2⟩
    · rintro z hz
      obtain rfl := mem_singleton_iff.mp hz
      exact ⟨hA'q, hB'q⟩
  have hCA : range C'.curve ∩ range A'.curve = {C'.start} := by
    apply Subset.antisymm
    · intro z hz
      have hz' : z ∈ (γ.curve '' Icc s t) ∩ range A.curve := by
        refine ⟨?_, hA'sub hz.2⟩
        simpa only [C', pointGeodesicSubedge_range] using hz.1
      have he : z = γ.curve s := mem_singleton_iff.mp (hsmeet ▸ hz')
      exact mem_singleton_iff.mpr he
    · rintro z hz
      obtain rfl := mem_singleton_iff.mp hz
      refine ⟨⟨⟨0, by norm_num⟩, C'.curve_start⟩, ?_⟩
      exact ⟨⟨1, by norm_num⟩, A'.curve_finish.trans hC's.symm⟩
  have hCB : range C'.curve ∩ range B'.curve = {C'.finish} := by
    apply Subset.antisymm
    · intro z hz
      have hz' : z ∈ (γ.curve '' Icc s t) ∩ range B.curve := by
        refine ⟨?_, hB'sub hz.2⟩
        simpa only [C', pointGeodesicSubedge_range] using hz.1
      have he : z = γ.curve t := mem_singleton_iff.mp (htmeet ▸ hz')
      exact mem_singleton_iff.mpr he
    · rintro z hz
      obtain rfl := mem_singleton_iff.mp hz
      refine ⟨⟨⟨1, by norm_num⟩, C'.curve_finish⟩, ?_⟩
      exact ⟨⟨1, by norm_num⟩, B'.curve_finish.trans hC'f.symm⟩
  exact ⟨⟨A', B', C', hA's, hB's, hC's, hC'f, hlegs, hCA, hCB⟩,
    hA'sub, hB'sub, hC'sub⟩

end RepulsiveCoulomb
