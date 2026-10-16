import LeanResearch.RepulsiveCoulomb.PointRadialPlaneArcArgumentTurn

/-! Preserve the genuine source lists while constructing the simple plane
cycle, and install the source-geodesic flux identity on every actual edge.
This avoids applying a geodesic formula to an arbitrary regular plane arc. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The literal source lists of a simple minimizing bigon produce the simple
closed plane cycle together with actual argument-turn data on every edge.
The source intervals remain available for proving passage-angle bounds. -/
theorem exists_pointConformal_simple_radial_C1_bigon_argument_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q}) :
    ∃ es₁ : List (PointRadialC1ArcPiece ha y γ₁),
    ∃ es₂ : List (PointRadialC1ArcPiece ha y γ₂),
      PointRadialC1ArcChain ha y γ₁ ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ es₁ ∧
      PointRadialC1ArcChain ha y γ₂ ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ es₂ ∧
      let L := es₁.map PointRadialC1ArcPiece.toPlane ++
        ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
      PointRadialC1PlaneChain ha y p p L ∧ 2 ≤ L.length ∧
        pointRadialC1PlaneCarrier L = range γ₁ ∪ range γ₂ ∧
        L.Pairwise (fun e f => Disjoint
          (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) ∧
        ∀ e ∈ L, e.HasArgumentTurn := by
  obtain ⟨es₁, es₂, h₁, h₂, hloop, hlen, hcarrier⟩ :=
    exists_pointConformal_radial_C1_bigon_cyclic_chain ha y hpq γ₁ γ₂
      h10 h11 h20 h21 hd₁ hd₂
  have hi₁ := pointConformal_geodesic_injective ha y hpq γ₁ hd₁
  have hi₂ := pointConformal_geodesic_injective ha y hpq γ₂ hd₂
  have hcross := simple_bigon_halfOpen_images_disjoint hi₁ hi₂ h11 h20 hmeet
  refine ⟨es₁, es₂, h₁, h₂, hloop, hlen, hcarrier, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨h₁.toPlane_halfOpen_pairwise hi₁, h₂.toPlane_reverse_halfOpen_pairwise hi₂, ?_⟩
    intro e he f hf
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
    rw [PointRadialC1PlaneArc.reverse_halfOpen_image]
    exact hcross.mono (h₁.halfOpen_subset_total hi₁ he₀)
      (h₂.reverseHalfOpen_subset_total hi₂ hf₀)
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      exact f.toPlane_hasArgumentTurn hpq h10 hd₁
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact (g.toPlane_hasArgumentTurn hpq h20 hd₂).reverse

end RepulsiveCoulomb
