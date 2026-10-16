module

public import LeanResearch.RepulsiveCoulomb.JordanCollarDeletion
public import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.StripLocal
public import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.PolygonalJordan

@[expose] public section

/-! The actual prescribed-neighborhood polygon collar has one connected exterior
side. Consequently removing a filled polygon preserves connectedness of an open
connected neighborhood containing it. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem jordan_connected_region_dichotomy {C S : Set Plane}
    (hC : IsSeparating C) (hS : IsConnected S) (hdis : Disjoint S C) :
    S ⊆ inside C ∨ S ⊆ outside C := by
  obtain ⟨W, V, hWV, hsub⟩ := hC.exists_isRegionPair_subset hS.isPreconnected hS.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hsub
  · exact Or.inr hsub

theorem jordan_collar_outside_connected {C N L R : Set Plane}
    (hC : IsSeparating C) (hN : IsOpen N) (hCN : C ⊆ N)
    (hL : IsConnected L) (hR : IsConnected R) (hcover : N \ C = L ∪ R) :
    IsConnected (N ∩ outside C) := by
  have hl : L ⊆ N \ C := by rw [hcover]; exact subset_union_left
  have hr : R ⊆ N \ C := by rw [hcover]; exact subset_union_right
  have hld : Disjoint L C := Set.disjoint_left.mpr (fun z hz hc => (hl hz).2 hc)
  have hrd : Disjoint R C := Set.disjoint_left.mpr (fun z hz hc => (hr hz).2 hc)
  obtain ⟨c, hc⟩ := hC.isJordanCurve.nonempty
  have hci : c ∈ closure (inside C) := frontier_subset_closure (hC.frontier_inside.symm ▸ hc)
  have hco : c ∈ closure (outside C) := frontier_subset_closure (hC.frontier_outside.symm ▸ hc)
  obtain ⟨xi, hxiN, hxi⟩ := mem_closure_iff.mp hci N hN (hCN hc)
  obtain ⟨xo, hxoN, hxo⟩ := mem_closure_iff.mp hco N hN (hCN hc)
  have hxiLR : xi ∈ L ∪ R := hcover ▸ (show xi ∈ N \ C from ⟨hxiN, inside_subset_compl hxi⟩)
  have hxoLR : xo ∈ L ∪ R := hcover ▸ (show xo ∈ N \ C from ⟨hxoN, outside_subset_compl hxo⟩)
  have heq (S T : Set Plane) (hs : S ⊆ N \ C) (hc : N \ C = S ∪ T)
      (hso : S ⊆ outside C) (hti : T ⊆ inside C) : N ∩ outside C = S := by
    apply Set.Subset.antisymm
    · intro z hz
      have hm : z ∈ S ∪ T := hc ▸ (show z ∈ N \ C from ⟨hz.1, outside_subset_compl hz.2⟩)
      exact hm.resolve_right (fun ht => Set.disjoint_left.mp disjoint_inside_outside (hti ht) hz.2)
    · exact fun z hz => ⟨(hs hz).1, hso hz⟩
  rcases jordan_connected_region_dichotomy hC hL hld with hli | hlo
  · rcases jordan_connected_region_dichotomy hC hR hrd with hri | hro
    · have hi := hxoLR.elim (fun h => hli h) (fun h => hri h)
      exact (Set.disjoint_left.mp disjoint_inside_outside hi hxo).elim
    · rw [heq R L hr (hcover.trans (union_comm L R)) hro hli]
      exact hR
  · rcases jordan_connected_region_dichotomy hC hR hrd with hri | hro
    · rw [heq L R hl hcover hlo hri]
      exact hL
    · have ho := hxiLR.elim (fun h => hlo h) (fun h => hro h)
      exact (Set.disjoint_left.mp disjoint_inside_outside hxi ho).elim

theorem polygon_connected_inter_outside {n : ℕ} (P : ClosedPolygon n)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsConnected U)
    (hKU : closure (inside P.carrier) ⊆ U) :
    IsConnected (U ∩ outside P.carrier) := by
  have hC := P.isSeparating_carrier
  have hCU : P.carrier ⊆ U := fun z hz => hKU
    (frontier_subset_closure (hC.frontier_inside.symm ▸ hz))
  obtain ⟨N, L, R, hN, hCN, hNU, _, _, hL, hR, _, hcover, _, _⟩ :=
    P.exists_two_sided_collar hU hCU
  exact connected_inter_outside_of_exterior_collar hC hU hUc hKU hN hCN hNU
    (jordan_collar_outside_connected hC hN hCN hL hR hcover)

end RepulsiveCoulomb
