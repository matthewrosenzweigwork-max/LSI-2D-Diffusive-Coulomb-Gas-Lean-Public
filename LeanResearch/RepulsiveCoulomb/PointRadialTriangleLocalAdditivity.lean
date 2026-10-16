module

public import LeanResearch.RepulsiveCoulomb.PointRadialC1PassageAngle
public import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleSubedges
public import LeanResearch.RepulsiveCoulomb.PointRadialC1PlaneArc

@[expose] public section

/-! Actual joined-pair metric additivity in the source-retaining triangular
macro-list. A same-source join uses the original minimizing identity. A join
of the two legs is forced to be the retained locally additive vertex q.
Cross/leg joins are exactly the two excluded outer vertices. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem triangle_piece_mem_range
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {γ : Icc (0 : ℝ) 1 → ℂ} (e : PointRadialC1ArcPiece ha y γ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : e.curve t ∈ range γ := by
  have hm : e.curve t ∈ γ '' Icc e.start e.finish := by
    rw [← e.image]
    exact ⟨t, ht, rfl⟩
  obtain ⟨u, hu, heq⟩ := hm
  exact ⟨u, heq⟩

private theorem triangle_source_join_additive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) (e f : PointRadialC1ArcPiece ha y E.curve)
    (hj : e.curve 1 = f.curve 0) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (pointSmoothConformalEDist a y (e.curve s) (f.curve t)).toReal =
      (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal +
        (pointSmoothConformalEDist a y (e.curve 1) (f.curve t)).toReal := by
  have hi := pointGeodesicTree_edges_injective ha y E
  have hsource : e.finish = f.start := hi ((e.at_one.symm.trans hj).trans f.at_zero)
  simpa only [e.at_one] using e.join_metric_additive f hsource E.geodesic hs ht

private theorem triangle_metric_additive_symm
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {x p z : ℂ}
    (h : (pointSmoothConformalEDist a y x z).toReal =
      (pointSmoothConformalEDist a y x p).toReal + (pointSmoothConformalEDist a y p z).toReal) :
    (pointSmoothConformalEDist a y z x).toReal =
      (pointSmoothConformalEDist a y z p).toReal + (pointSmoothConformalEDist a y p x).toReal := by
  rw [pointSmoothConformalEDist_comm a y z x, h,
    pointSmoothConformalEDist_comm a y x p, pointSmoothConformalEDist_comm a y p z]
  exact add_comm _ _

private theorem triangle_cross_left_vertex
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {q z : ℂ}
    (T : PointSimpleGeodesicTriangle a y q)
    (hzC : z ∈ range T.cross.curve) (hzL : z ∈ range T.left.curve) : z = T.left.finish := by
  have hz : z ∈ range T.cross.curve ∩ range T.left.curve := ⟨hzC, hzL⟩
  rw [T.cross_left] at hz
  exact (mem_singleton_iff.mp hz).trans T.cross_start

private theorem triangle_cross_right_vertex
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {q z : ℂ}
    (T : PointSimpleGeodesicTriangle a y q)
    (hzC : z ∈ range T.cross.curve) (hzR : z ∈ range T.right.curve) : z = T.right.finish := by
  have hz : z ∈ range T.cross.curve ∩ range T.right.curve := ⟨hzC, hzR⟩
  rw [T.cross_right] at hz
  exact (mem_singleton_iff.mp hz).trans T.cross_finish

private theorem triangle_legs_vertex
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {q z : ℂ}
    (T : PointSimpleGeodesicTriangle a y q)
    (hzL : z ∈ range T.left.curve) (hzR : z ∈ range T.right.curve) : z = q := by
  have hz : z ∈ range T.left.curve ∩ range T.right.curve := ⟨hzL, hzR⟩
  rw [T.legs_meet] at hz
  exact mem_singleton_iff.mp hz

/-- Every actual joined pair away from the two outer triangle vertices is
additive for sufficiently near points. The retained q-vertex uses exactly the
supplied original range-local metric identity, with radius min(r₀,1). -/
theorem point_radial_triangle_internal_join_locally_additive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {q : ℂ} (T : PointSimpleGeodesicTriangle a y q) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hlocal : ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
      (pointSmoothConformalEDist a y x q).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y z q).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y x z).toReal =
        (pointSmoothConformalEDist a y x q).toReal + (pointSmoothConformalEDist a y q z).toReal)
    (esL : List (PointRadialC1ArcPiece ha y T.left.curve))
    (esC : List (PointRadialC1ArcPiece ha y T.cross.curve))
    (esR : List (PointRadialC1ArcPiece ha y T.right.curve)) :
    let L := (esL.map PointRadialC1ArcPiece.toPlane ++ esC.map PointRadialC1ArcPiece.toPlane) ++
      ((esR.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ f ∈ L, e.curve 1 = f.curve 0 →
      e.curve 1 ≠ T.left.finish → e.curve 1 ≠ T.right.finish →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal ≤ min r₀ 1 →
      (pointSmoothConformalEDist a y (f.curve t) (e.curve 1)).toReal ≤ min r₀ 1 →
      (pointSmoothConformalEDist a y (e.curve s) (f.curve t)).toReal =
        (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal +
          (pointSmoothConformalEDist a y (e.curve 1) (f.curve t)).toReal := by
  intro L e he f hf hj hA hB s t hs ht hsnear htnear
  have hsR : 1 - s ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
  have htR : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
          exact triangle_source_join_additive ha y T.left e₀ f₀ hj hs ht
        · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
          have hzL : e₀.curve 1 ∈ range T.left.curve := ⟨e₀.finish, e₀.at_one.symm⟩
          have hzC : e₀.curve 1 ∈ range T.cross.curve :=
            ⟨f₀.start, f₀.at_zero.symm.trans hj.symm⟩
          exact False.elim (hA (triangle_cross_left_vertex T hzC hzL))
      · obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
        obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
        change e₀.curve 1 = f₀.curve (1 - (0 : ℝ)) at hj
        rw [sub_zero] at hj
        have hzq : e₀.curve 1 = q := triangle_legs_vertex T
          ⟨e₀.finish, e₀.at_one.symm⟩ ⟨f₀.finish, f₀.at_one.symm.trans hj.symm⟩
        change (pointSmoothConformalEDist a y (e₀.curve s) (e₀.curve 1)).toReal ≤ min r₀ 1 at hsnear
        change (pointSmoothConformalEDist a y (f₀.curve (1 - t)) (e₀.curve 1)).toReal ≤ min r₀ 1 at htnear
        rw [hzq] at hsnear htnear
        simpa only [PointRadialC1ArcPiece.toPlane, PointRadialC1PlaneArc.reverse, hzq] using
          hlocal _ (triangle_piece_mem_range e₀ hs) _ (triangle_piece_mem_range f₀ htR)
            (hsnear.trans (min_le_left _ _)) (htnear.trans (min_le_left _ _))
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
          have hzC : e₀.curve 1 ∈ range T.cross.curve := ⟨e₀.finish, e₀.at_one.symm⟩
          have hzL : e₀.curve 1 ∈ range T.left.curve :=
            ⟨f₀.start, f₀.at_zero.symm.trans hj.symm⟩
          exact False.elim (hA (triangle_cross_left_vertex T hzC hzL))
        · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
          exact triangle_source_join_additive ha y T.cross e₀ f₀ hj hs ht
      · obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
        obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
        change e₀.curve 1 = f₀.curve (1 - (0 : ℝ)) at hj
        rw [sub_zero] at hj
        have hzC : e₀.curve 1 ∈ range T.cross.curve := ⟨e₀.finish, e₀.at_one.symm⟩
        have hzR : e₀.curve 1 ∈ range T.right.curve :=
          ⟨f₀.finish, f₀.at_one.symm.trans hj.symm⟩
        exact False.elim (hB (triangle_cross_right_vertex T hzC hzR))
  · obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        change e₀.curve (1 - (1 : ℝ)) = f₀.curve 0 at hj
        rw [sub_self] at hj
        have hzq : e₀.curve 0 = q := triangle_legs_vertex T
          ⟨f₀.start, f₀.at_zero.symm.trans hj.symm⟩ ⟨e₀.start, e₀.at_zero.symm⟩
        change (pointSmoothConformalEDist a y (e₀.curve (1 - s)) (e₀.curve (1 - (1 : ℝ)))).toReal ≤ min r₀ 1 at hsnear
        change (pointSmoothConformalEDist a y (f₀.curve t) (e₀.curve (1 - (1 : ℝ)))).toReal ≤ min r₀ 1 at htnear
        rw [sub_self, hzq] at hsnear htnear
        have hadd := hlocal _ (triangle_piece_mem_range f₀ ht) _ (triangle_piece_mem_range e₀ hsR)
          (htnear.trans (min_le_left _ _)) (hsnear.trans (min_le_left _ _))
        simpa only [PointRadialC1ArcPiece.toPlane, PointRadialC1PlaneArc.reverse, sub_self, hzq] using
          triangle_metric_additive_symm a y hadd
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        change e₀.curve (1 - (1 : ℝ)) = f₀.curve 0 at hj
        rw [sub_self] at hj
        have hzC : e₀.curve 0 ∈ range T.cross.curve :=
          ⟨f₀.start, f₀.at_zero.symm.trans hj.symm⟩
        have hzR : e₀.curve 0 ∈ range T.right.curve := ⟨e₀.start, e₀.at_zero.symm⟩
        apply False.elim
        apply hB
        simpa only [PointRadialC1ArcPiece.toPlane, PointRadialC1PlaneArc.reverse, sub_self] using
          triangle_cross_right_vertex T hzC hzR
    · obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
      obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
      change e₀.curve (1 - (1 : ℝ)) = f₀.curve (1 - (0 : ℝ)) at hj
      rw [sub_self, sub_zero] at hj
      have hadd := triangle_source_join_additive ha y T.right f₀ e₀ hj.symm htR hsR
      rw [← hj] at hadd
      simpa only [PointRadialC1ArcPiece.toPlane, PointRadialC1PlaneArc.reverse, sub_self] using
        triangle_metric_additive_symm a y hadd

end RepulsiveCoulomb
