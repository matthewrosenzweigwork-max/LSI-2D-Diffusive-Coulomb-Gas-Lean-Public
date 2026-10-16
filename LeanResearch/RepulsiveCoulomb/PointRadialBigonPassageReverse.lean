import LeanResearch.RepulsiveCoulomb.PointRadialBigonPassage

/-! The actual bigon source list retains puncture-free open edges and its
internal metric additivity under the literal positive-traversal reversal. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem point_radial_bigon_piece_no_interior_puncture
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (es₁ : List (PointRadialC1ArcPiece ha y γ₁))
    (es₂ : List (PointRadialC1ArcPiece ha y γ₂)) :
    let L := es₁.map PointRadialC1ArcPiece.toPlane ++
      ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ t ∈ Ioo (0 : ℝ) 1, e.curve t ∉ pointPunctures a y := by
  dsimp only
  intro e he t ht
  rcases List.mem_append.mp he with he | he
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    exact e₀.curve_no_interior_puncture (pointConformal_geodesic_injective ha y hpq γ₁ hd₁) ht
  · obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
    exact e₀.curve_no_interior_puncture (pointConformal_geodesic_injective ha y hpq γ₂ hd₂)
      (by constructor <;> linarith [ht.1, ht.2])

theorem point_radial_bigon_internal_reversed_join_additive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q})
    (es₁ : List (PointRadialC1ArcPiece ha y γ₁))
    (es₂ : List (PointRadialC1ArcPiece ha y γ₂)) :
    let L := es₁.map PointRadialC1ArcPiece.toPlane ++
      ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ f ∈ L, e.reverse.curve 1 = f.reverse.curve 0 →
      e.reverse.curve 1 ≠ p → e.reverse.curve 1 ≠ q →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      (pointSmoothConformalEDist a y (e.reverse.curve s) (f.reverse.curve t)).toReal =
        (pointSmoothConformalEDist a y (e.reverse.curve s) (e.reverse.curve 1)).toReal +
          (pointSmoothConformalEDist a y (e.reverse.curve 1) (f.reverse.curve t)).toReal := by
  dsimp only
  intro e he f hf hj hp hq s t hs ht
  have hjoin : f.curve 1 = e.curve 0 := by
    simpa only [PointRadialC1PlaneArc.reverse, sub_self, sub_zero] using hj.symm
  have hnp : f.curve 1 ≠ p := by
    rw [hjoin]
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using hp
  have hnq : f.curve 1 ≠ q := by
    rw [hjoin]
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using hq
  have hadd := point_radial_bigon_internal_join_additive ha y hpq γ₁ γ₂ hd₁ hd₂ hmeet es₁ es₂
    f hf e he hjoin hnp hnq (1 - t) (1 - s)
    (by constructor <;> linarith [ht.1, ht.2])
    (by constructor <;> linarith [hs.1, hs.2])
  rw [hjoin] at hadd
  change (pointSmoothConformalEDist a y (e.curve (1 - s)) (f.curve (1 - t))).toReal =
    (pointSmoothConformalEDist a y (e.curve (1 - s)) (e.curve (1 - (1 : ℝ)))).toReal +
      (pointSmoothConformalEDist a y (e.curve (1 - (1 : ℝ))) (f.curve (1 - t))).toReal
  rw [sub_self, pointSmoothConformalEDist_comm a y (e.curve (1 - s)) (f.curve (1 - t)), hadd,
    pointSmoothConformalEDist_comm a y (f.curve (1 - t)) (e.curve 0),
    pointSmoothConformalEDist_comm a y (e.curve 0) (e.curve (1 - s))]
  exact add_comm _ _

end RepulsiveCoulomb
