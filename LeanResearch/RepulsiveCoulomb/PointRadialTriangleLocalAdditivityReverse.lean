import LeanResearch.RepulsiveCoulomb.PointRadialTriangleLocalAdditivity

/-! Literal traversal reversal preserves the actual triangle's local join
additivity. The threshold remains min(r₀,1), and the only exceptional physical
vertices remain the two outer vertices of the original triangle. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Local additivity for the reversed original triangular macro-family. -/
theorem point_radial_triangle_internal_reversed_join_locally_additive
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
    ∀ e ∈ L, ∀ f ∈ L, e.reverse.curve 1 = f.reverse.curve 0 →
      e.reverse.curve 1 ≠ T.left.finish → e.reverse.curve 1 ≠ T.right.finish →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      (pointSmoothConformalEDist a y (e.reverse.curve s) (e.reverse.curve 1)).toReal ≤ min r₀ 1 →
      (pointSmoothConformalEDist a y (f.reverse.curve t) (e.reverse.curve 1)).toReal ≤ min r₀ 1 →
      (pointSmoothConformalEDist a y (e.reverse.curve s) (f.reverse.curve t)).toReal =
        (pointSmoothConformalEDist a y (e.reverse.curve s) (e.reverse.curve 1)).toReal +
          (pointSmoothConformalEDist a y (e.reverse.curve 1) (f.reverse.curve t)).toReal := by
  intro L e he f hf hj hA hB s t hs ht hsnear htnear
  have hjoin : f.curve 1 = e.curve 0 := by
    simpa only [PointRadialC1PlaneArc.reverse, sub_self, sub_zero] using hj.symm
  have hnA : f.curve 1 ≠ T.left.finish := by
    rw [hjoin]
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using hA
  have hnB : f.curve 1 ≠ T.right.finish := by
    rw [hjoin]
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using hB
  have hfirst : (pointSmoothConformalEDist a y (f.curve (1 - t)) (f.curve 1)).toReal ≤ min r₀ 1 := by
    rw [hjoin]
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using htnear
  have hsecond : (pointSmoothConformalEDist a y (e.curve (1 - s)) (f.curve 1)).toReal ≤ min r₀ 1 := by
    rw [hjoin]
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using hsnear
  have hadd := point_radial_triangle_internal_join_locally_additive ha y T hr₀ hlocal esL esC esR
    f hf e he hjoin hnA hnB (1 - t) (1 - s)
    (by constructor <;> linarith [ht.1, ht.2])
    (by constructor <;> linarith [hs.1, hs.2]) hfirst hsecond
  rw [hjoin] at hadd
  change (pointSmoothConformalEDist a y (e.curve (1 - s)) (f.curve (1 - t))).toReal =
    (pointSmoothConformalEDist a y (e.curve (1 - s)) (e.curve (1 - (1 : ℝ)))).toReal +
      (pointSmoothConformalEDist a y (e.curve (1 - (1 : ℝ))) (f.curve (1 - t))).toReal
  rw [sub_self, pointSmoothConformalEDist_comm a y (e.curve (1 - s)) (f.curve (1 - t)), hadd,
    pointSmoothConformalEDist_comm a y (f.curve (1 - t)) (e.curve 0),
    pointSmoothConformalEDist_comm a y (e.curve 0) (e.curve (1 - s))]
  exact add_comm _ _

end RepulsiveCoulomb
