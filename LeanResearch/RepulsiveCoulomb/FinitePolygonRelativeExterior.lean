module

public import LeanResearch.RepulsiveCoulomb.FinitePolygonEnclosingDomain

@[expose] public section

/-! A connected zero-free region containing the observation set outside the
filled interiors of precisely those polygonal contours that meet it. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem finite_polygon_relative_exterior {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι) {B : Set Plane}
    (hB : IsConnected B)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => (P i).carrier)) :
    ∃ R : Set Plane, IsConnected R ∧ Disjoint R (⋃ i ∈ s, (P i).carrier) ∧
      ∀ x ∈ B, (∀ i ∈ s, ((P i).carrier ∩ B).Nonempty → x ∉ closure (inside (P i).carrier)) → x ∈ R := by
  classical
  obtain ⟨U,D,hU,hUc,hBU,hDs,hfill,hcover,hmiss⟩ := finite_polygon_enclosing_domain n P s hB hdis
  let R := U ∩ ⋂ i ∈ D, outside (P i).carrier
  refine ⟨R, finite_polygon_local_exterior_connected n P D hU hUc hfill
    (hdis.mono (by intro i hi; exact hDs hi)), ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxC
    obtain ⟨i,hxC⟩ := mem_iUnion.mp hxC
    obtain ⟨hi,hxC⟩ := mem_iUnion.mp hxC
    have hiD := hcover i hi ⟨x,hxC,hx.1⟩
    have hxo : x ∈ outside (P i).carrier := mem_iInter.mp (mem_iInter.mp hx.2 i) hiD
    exact outside_subset_compl hxo hxC
  · intro x hx havoid
    refine ⟨hBU hx, ?_⟩
    apply mem_iInter.mpr
    intro i
    apply mem_iInter.mpr
    intro hiD
    by_cases hmeet : ((P i).carrier ∩ B).Nonempty
    · rw [← jordan_compl_filled_eq_outside (P i).isSeparating_carrier]
      exact havoid i (hDs hiD) hmeet
    · apply hmiss i hiD ?_ hx
      apply Set.disjoint_left.mpr
      intro z hzB hzC
      exact hmeet ⟨z,hzC,hzB⟩

end RepulsiveCoulomb
