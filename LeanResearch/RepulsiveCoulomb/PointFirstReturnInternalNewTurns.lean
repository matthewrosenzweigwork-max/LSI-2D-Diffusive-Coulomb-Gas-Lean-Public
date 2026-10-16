module

public import LeanResearch.RepulsiveCoulomb.PointFirstReturnActualFiniteFamily
public import LeanResearch.RepulsiveCoulomb.PointRadialPlanePassageAngle
public import LeanResearch.RepulsiveCoulomb.PointRadialPhysicalTurn
public import LeanResearch.RepulsiveCoulomb.PointPhysicalDirectedSector

@[expose] public section

/-! Successor draft. Internal new-ray vertices are identified by actual
frontier avoidance. Both incident representatives then come from the same
stopped metric ray. Its exact metric additivity proves nonpositive actual
physical turn, including at ambient atoms and after global traversal reversal. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem PointBoundaryRadialChainOn.curve_mem_boundary
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {P : Set ℂ} {b : unitInterval → ℂ} {s t : unitInterval}
    {L : List (PointRadialC1PlaneArc ha y)}
    (D : PointBoundaryRadialChainOn ha y b s t L)
    (hb : ∀ u, b u ∈ frontier P)
    {e : PointRadialC1PlaneArc ha y} (he : e ∈ L) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    e.curve u ∈ frontier P := by
  have hm : e.curve u ∈ pointRadialC1PlaneCarrier L :=
    mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, ⟨u, hu, rfl⟩⟩⟩
  rw [D.carrier] at hm
  obtain ⟨v, hv, heq⟩ := hm
  exact heq ▸ hb v

theorem firstReturn_metric_additive_symm
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {x p z : ℂ}
    (h : (pointSmoothConformalEDist a y x z).toReal =
      (pointSmoothConformalEDist a y x p).toReal + (pointSmoothConformalEDist a y p z).toReal) :
    (pointSmoothConformalEDist a y z x).toReal =
      (pointSmoothConformalEDist a y z p).toReal + (pointSmoothConformalEDist a y p x).toReal := by
  rw [pointSmoothConformalEDist_comm a y z x, h,
    pointSmoothConformalEDist_comm a y x p, pointSmoothConformalEDist_comm a y p z]
  exact add_comm _ _

/-- An actual join off the old frontier has two new-ray sources. No turn or
angle premise appears: all pairs are additive in the original metric. -/
theorem firstReturn_new_source_join_additive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (old : List (PointRadialC1PlaneArc ha y))
    (hOld : ∀ e ∈ old, ∀ u ∈ Icc (0 : ℝ) 1, e.curve u ∈ frontier P)
    (γ : unitInterval → ℂ) (hγi : Function.Injective γ) {d : ℝ}
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal = |v.1 - u.1| * d)
    (fresh : List (PointRadialC1ArcPiece ha y γ)) :
    let L := old ++ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ f ∈ L, e.curve 1 = f.curve 0 → e.curve 1 ∉ frontier P →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        (pointSmoothConformalEDist a y (e.curve s) (f.curve t)).toReal =
          (pointSmoothConformalEDist a y (e.curve s) (e.curve 1)).toReal +
            (pointSmoothConformalEDist a y (e.curve 1) (f.curve t)).toReal := by
  intro L e he f hf hj hnot s t hs ht
  have heNew : e ∈ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse :=
    (List.mem_append.mp he).resolve_left (fun he => hnot (hOld e he 1 (by norm_num)))
  have hfNew : f ∈ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse := by
    apply (List.mem_append.mp hf).resolve_left
    intro hfOld
    exact hnot (hj.symm ▸ hOld f hfOld 0 (by norm_num))
  obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp heNew)
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
  obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hfNew)
  obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
  have hj' : f₀.curve 1 = e₀.curve 0 := by
    simpa only [PointRadialC1ArcPiece.toPlane, PointRadialC1PlaneArc.reverse,
      sub_self, sub_zero] using hj.symm
  have hsource : f₀.finish = e₀.start :=
    hγi ((f₀.at_one.symm.trans hj').trans e₀.at_zero)
  have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hadd := f₀.join_metric_additive e₀ hsource hd ht' hs'
  rw [← f₀.at_one, hj'] at hadd
  simpa only [PointRadialC1ArcPiece.toPlane, PointRadialC1PlaneArc.reverse, sub_self] using
    firstReturn_metric_additive_symm a y hadd

/-- Global orientation reversal preserves the derived metric additivity. -/
theorem firstReturn_new_source_reversed_join_additive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (old : List (PointRadialC1PlaneArc ha y))
    (hOld : ∀ e ∈ old, ∀ u ∈ Icc (0 : ℝ) 1, e.curve u ∈ frontier P)
    (γ : unitInterval → ℂ) (hγi : Function.Injective γ) {d : ℝ}
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal = |v.1 - u.1| * d)
    (fresh : List (PointRadialC1ArcPiece ha y γ)) :
    let L := old ++ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ f ∈ L, e.reverse.curve 1 = f.reverse.curve 0 →
      e.reverse.curve 1 ∉ frontier P →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        (pointSmoothConformalEDist a y (e.reverse.curve s) (f.reverse.curve t)).toReal =
          (pointSmoothConformalEDist a y (e.reverse.curve s) (e.reverse.curve 1)).toReal +
            (pointSmoothConformalEDist a y (e.reverse.curve 1) (f.reverse.curve t)).toReal := by
  intro L e he f hf hj hnot s t hs ht
  have hj' : f.curve 1 = e.curve 0 := by
    simpa only [PointRadialC1PlaneArc.reverse, sub_self, sub_zero] using hj.symm
  have hn : f.curve 1 ∉ frontier P := by
    rw [hj']
    simpa only [PointRadialC1PlaneArc.reverse, sub_self] using hnot
  have hadd := firstReturn_new_source_join_additive ha y old hOld γ hγi hd fresh
    f hf e he hj' hn (1 - t) (1 - s)
    (by constructor <;> linarith [ht.1, ht.2])
    (by constructor <;> linarith [hs.1, hs.2])
  rw [hj'] at hadd
  simpa only [PointRadialC1PlaneArc.reverse, sub_self] using
    firstReturn_metric_additive_symm a y hadd

/-- The actual full mixed-GB turn at any new vertex off the old frontier is
nonpositive. Ambient positive atoms are included; the original metric ray is
never differentiated. The source lists come from the actual-family constructor. -/
theorem PointFirstReturnFiniteGBData.new_vertex_turn_nonpos
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P U V : Set ℂ} (old : List (PointRadialC1PlaneArc ha y))
    (hOld : ∀ e ∈ old, ∀ u ∈ Icc (0 : ℝ) 1, e.curve u ∈ frontier P)
    (γ : unitInterval → ℂ) (hγi : Function.Injective γ) {d : ℝ}
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal = |v.1 - u.1| * d)
    (fresh : List (PointRadialC1ArcPiece ha y γ))
    {n : ℕ} {arcs : ℕ → PointRadialC1PlaneArc ha y}
    (hmem : ∀ k, arcs k ∈ old ++
      ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse)
    (D : PointFirstReturnFiniteGBData ha y arcs n U V)
    {k : ℕ} (hk : k ≤ n) (hnot : (D.oriented k).curve 0 ∉ frontier P) :
    Real.pi - (1 + coalescedPointExponent a y ((D.oriented k).curve 0) / 2) * D.angle k ≤ 0 := by
  obtain ⟨G, _, _, _, _⟩ := D.radial_corner k hk
  let j : ℕ := G.order n
  have hj : (D.oriented (j)).curve 1 = (D.oriented k).curve 0 := by
    simpa only [G.order_zero] using G.closing
  have hnot' : (D.oriented (j)).curve 1 ∉ frontier P := by rwa [hj]
  have hadd : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      (pointSmoothConformalEDist a y ((D.oriented (j)).curve s) ((D.oriented k).curve t)).toReal =
        (pointSmoothConformalEDist a y ((D.oriented (j)).curve s) ((D.oriented (j)).curve 1)).toReal +
          (pointSmoothConformalEDist a y ((D.oriented (j)).curve 1) ((D.oriented k).curve t)).toReal := by
    rcases D.orientation with heq | heq
    · rw [heq] at hj hnot' ⊢
      exact firstReturn_new_source_join_additive ha y old hOld γ hγi hd fresh
        _ (hmem _) _ (hmem _) hj hnot'
    · rw [heq] at hj hnot' ⊢
      exact firstReturn_new_source_reversed_join_additive ha y old hOld γ hγi hd fresh
        _ (hmem _) _ (hmem _) hj hnot'
  have hraw := (D.oriented (j)).local_passage_sector_turns_nonpos
    (D.oriented k) hj (show (0 : ℝ) < 1 by norm_num) (fun s t hs ht _ _ => hadd s t hs ht)
  rw [hj] at hraw
  have hphysical := (D.oriented (j)).physical_sector_turns_nonpos (D.oriented k) hj
    (coalescedPointExponent a y ((D.oriented k).curve 0) / 2) hraw.1 hraw.2
  have hturn := G.directed_turn_nonpos (fun i _ => (D.oriented i).smooth)
    (fun i _ => (D.oriented i).regular) hphysical.1 hphysical.2
  simpa only [add_comm] using hturn

end RepulsiveCoulomb
