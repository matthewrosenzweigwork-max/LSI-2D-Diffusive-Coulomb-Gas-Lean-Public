import LeanResearch.RepulsiveCoulomb.FinitePolygonRelativeExterior

/-! One strict level side in any connected observation set is covered by the
bounded interiors of exactly the polygonal level components meeting that set. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem finite_polygon_level_sign_cover {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι) {B : Set Plane}
    (hB : IsConnected B)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => (P i).carrier))
    {f : Plane → ℝ} (hf : Continuous f) (t : ℝ)
    (hlevel : f ⁻¹' {t} = ⋃ i ∈ s, (P i).carrier) :
    (B ∩ {x | f x < t} ⊆ ⋃ i ∈ s, ⋃ (_ : ((P i).carrier ∩ B).Nonempty), inside (P i).carrier) ∨
    (B ∩ {x | t < f x} ⊆ ⋃ i ∈ s, ⋃ (_ : ((P i).carrier ∩ B).Nonempty), inside (P i).carrier) := by
  classical
  obtain ⟨R,hR,hRC,hcover⟩ := finite_polygon_relative_exterior n P s hB hdis
  have hn : ∀ x ∈ R, f x ≠ t := by
    intro x hx hxt
    have hxl : x ∈ f ⁻¹' {t} := hxt
    rw [hlevel] at hxl
    exact Set.disjoint_left.mp hRC hx hxl
  have houtside : ∀ x ∈ B, f x ≠ t →
      x ∉ (⋃ i ∈ s, ⋃ (_ : ((P i).carrier ∩ B).Nonempty), inside (P i).carrier) → x ∈ R := by
    intro x hx hxt hnot
    apply hcover x hx
    intro i hi hmeet hxK
    rw [closure_eq_self_union_frontier, (P i).isSeparating_carrier.frontier_inside] at hxK
    rcases hxK with hxi | hxc
    · exact hnot (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, mem_iUnion.mpr ⟨hmeet,hxi⟩⟩⟩)
    · apply hxt
      have hxl : x ∈ ⋃ i ∈ s, (P i).carrier := mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hxc⟩⟩
      rw [← hlevel] at hxl
      exact hxl
  rcases hR.isPreconnected.mapsTo_Ioi_or_Iio hf.continuousOn hn with hpos | hneg
  · left
    intro x hx
    by_contra hnot
    have hxR := houtside x hx.1 (ne_of_lt hx.2) hnot
    have htpos : t < f x := hpos hxR
    exact (not_lt_of_ge htpos.le hx.2)
  · right
    intro x hx
    by_contra hnot
    have hxR := houtside x hx.1 (ne_of_gt hx.2) hnot
    have htneg : f x < t := hneg hxR
    exact (not_lt_of_ge htneg.le hx.2)

end RepulsiveCoulomb
