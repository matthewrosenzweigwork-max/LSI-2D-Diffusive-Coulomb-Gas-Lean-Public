module

public import LeanResearch.RepulsiveCoulomb.PointRadialPlaneArcArgumentTurn
public import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleSubedges

@[expose] public section

/-! The three genuine minimizing sides of an actual simple triangle supply
one finite cyclic radial macro-list, with source intervals, simplicity and
the conformal argument identity retained on every actual plane edge. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointSimpleGeodesicTriangle_radial_C1_argument_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {q : ℂ} (T : PointSimpleGeodesicTriangle a y q) :
    ∃ esL : List (PointRadialC1ArcPiece ha y T.left.curve),
    ∃ esC : List (PointRadialC1ArcPiece ha y T.cross.curve),
    ∃ esR : List (PointRadialC1ArcPiece ha y T.right.curve),
      PointRadialC1ArcChain ha y T.left.curve ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ esL ∧
      PointRadialC1ArcChain ha y T.cross.curve ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ esC ∧
      PointRadialC1ArcChain ha y T.right.curve ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ esR ∧
      let L := (esL.map PointRadialC1ArcPiece.toPlane ++ esC.map PointRadialC1ArcPiece.toPlane) ++
        ((esR.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
      PointRadialC1PlaneChain ha y q q L ∧ 3 ≤ L.length ∧
        pointRadialC1PlaneCarrier L = range T.left.curve ∪ range T.cross.curve ∪ range T.right.curve ∧
        L.Pairwise (fun e f => Disjoint
          (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) ∧
        ∀ e ∈ L, e.HasArgumentTurn := by
  obtain ⟨esL, hL, _, hneL, _⟩ := exists_pointConformal_finite_radial_C1_arc_chain
    ha y T.left.distinct T.left.curve T.left.geodesic
  obtain ⟨esC, hC, _, hneC, _⟩ := exists_pointConformal_finite_radial_C1_arc_chain
    ha y T.cross.distinct T.cross.curve T.cross.geodesic
  obtain ⟨esR, hR, _, hneR, _⟩ := exists_pointConformal_finite_radial_C1_arc_chain
    ha y T.right.distinct T.right.curve T.right.geodesic
  have hiL := pointGeodesicTree_edges_injective ha y T.left
  have hiC := pointGeodesicTree_edges_injective ha y T.cross
  have hiR := pointGeodesicTree_edges_injective ha y T.right
  have hPL := hL.toPlane
  have hPC := hC.toPlane
  have hPR := hR.toPlane
  rw [T.left.curve_start, T.left.curve_finish, T.left_start] at hPL
  rw [T.cross.curve_start, T.cross.curve_finish, T.cross_start, T.cross_finish] at hPC
  rw [T.right.curve_start, T.right.curve_finish, T.right_start] at hPR
  have hI : Icc (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ = univ := by
    apply eq_univ_of_forall
    intro u
    exact u.2
  have hmL := hL.toPlane_carrier (by norm_num)
  have hmC := hC.toPlane_carrier (by norm_num)
  have hmR := hR.toPlane_carrier (by norm_num)
  rw [hI, image_univ] at hmL hmC hmR
  have hLC : Disjoint (T.left.curve '' Ico (0 : Icc (0 : ℝ) 1) 1)
      (T.cross.curve '' Ico (0 : Icc (0 : ℝ) 1) 1) := by
    apply disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    have hz : z ∈ range T.cross.curve ∩ range T.left.curve := ⟨⟨t, htz⟩, ⟨s, hsz⟩⟩
    rw [T.cross_left] at hz
    have hze : z = T.left.finish := (mem_singleton_iff.mp hz).trans T.cross_start
    exact hs.2.ne (hiL ((hsz.trans hze).trans T.left.curve_finish.symm))
  have hLR : Disjoint (T.left.curve '' Ico (0 : Icc (0 : ℝ) 1) 1)
      (T.right.curve '' Ioc (0 : Icc (0 : ℝ) 1) 1) := by
    apply disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    have hz : z ∈ range T.left.curve ∩ range T.right.curve := ⟨⟨s, hsz⟩, ⟨t, htz⟩⟩
    rw [T.legs_meet] at hz
    have hze : z = q := mem_singleton_iff.mp hz
    exact ht.1.ne' (hiR ((htz.trans hze).trans (T.right.curve_start.trans T.right_start).symm))
  have hCR : Disjoint (T.cross.curve '' Ico (0 : Icc (0 : ℝ) 1) 1)
      (T.right.curve '' Ioc (0 : Icc (0 : ℝ) 1) 1) := by
    apply disjoint_left.mpr
    rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
    have hz : z ∈ range T.cross.curve ∩ range T.right.curve := ⟨⟨s, hsz⟩, ⟨t, htz⟩⟩
    rw [T.cross_right] at hz
    exact hs.2.ne (hiC ((hsz.trans (mem_singleton_iff.mp hz)).trans T.cross.curve_finish.symm))
  refine ⟨esL, esC, esR, hL, hC, hR, (hPL.append hPC).append hPR.reverse, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_reverse]
    have := List.length_pos_iff.mpr hneL
    have := List.length_pos_iff.mpr hneC
    have := List.length_pos_iff.mpr hneR
    omega
  · rw [pointRadialC1PlaneCarrier_append, pointRadialC1PlaneCarrier_append,
      pointRadialC1PlaneCarrier_reverse, hmL, hmC, hmR]
  · rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨hL.toPlane_halfOpen_pairwise hiL, hC.toPlane_halfOpen_pairwise hiC, ?_⟩,
      hR.toPlane_reverse_halfOpen_pairwise hiR, ?_⟩
    · intro e he f hf
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      exact hLC.mono (hL.halfOpen_subset_total hiL he₀) (hC.halfOpen_subset_total hiC hf₀)
    · intro e he f hf
      obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
      obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
      rw [PointRadialC1PlaneArc.reverse_halfOpen_image]
      rcases List.mem_append.mp he with he | he
      · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
        exact hLR.mono (hL.halfOpen_subset_total hiL he₀) (hR.reverseHalfOpen_subset_total hiR hf₀)
      · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
        exact hCR.mono (hC.halfOpen_subset_total hiC he₀) (hR.reverseHalfOpen_subset_total hiR hf₀)
  · intro e he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
        exact f.toPlane_hasArgumentTurn T.left.distinct T.left.curve_start T.left.geodesic
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
        exact f.toPlane_hasArgumentTurn T.cross.distinct T.cross.curve_start T.cross.geodesic
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact (g.toPlane_hasArgumentTurn T.right.distinct T.right.curve_start T.right.geodesic).reverse

end RepulsiveCoulomb
