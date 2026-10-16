module

public import LeanResearch.RepulsiveCoulomb.PointRadialTriangleArgumentTurn

@[expose] public section

/-! Active punctures occur only at actual vertices of the source-preserving
triangle macro-list, including on its literally reversed right-hand side. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem point_radial_triangle_piece_no_interior_puncture
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {q : ℂ} (T : PointSimpleGeodesicTriangle a y q)
    (esL : List (PointRadialC1ArcPiece ha y T.left.curve))
    (esC : List (PointRadialC1ArcPiece ha y T.cross.curve))
    (esR : List (PointRadialC1ArcPiece ha y T.right.curve)) :
    let L := (esL.map PointRadialC1ArcPiece.toPlane ++ esC.map PointRadialC1ArcPiece.toPlane) ++
      ((esR.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ t ∈ Ioo (0 : ℝ) 1, e.curve t ∉ pointPunctures a y := by
  dsimp only
  intro e he t ht
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact e₀.curve_no_interior_puncture (pointGeodesicTree_edges_injective ha y T.left) ht
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact e₀.curve_no_interior_puncture (pointGeodesicTree_edges_injective ha y T.cross) ht
  · obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
    exact e₀.curve_no_interior_puncture (pointGeodesicTree_edges_injective ha y T.right)
      (by constructor <;> linarith [ht.1, ht.2])

end RepulsiveCoulomb
