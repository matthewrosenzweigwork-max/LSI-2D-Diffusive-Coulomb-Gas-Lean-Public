module

public import LeanResearch.RepulsiveCoulomb.JordanDisjointNesting
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-! Removing a filled Jordan region from a connected open set preserves
connectedness when an actual connected exterior collar is present. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem closure_component_inter_open_subset {F : Set Plane} (hF : IsOpen F) (x : Plane) :
    closure (connectedComponentIn F x) ∩ F ⊆ connectedComponentIn F x := by
  intro z hz
  obtain ⟨w, hwz, hwx⟩ := mem_closure_iff.mp hz.1 (connectedComponentIn F z)
    hF.connectedComponentIn (mem_connectedComponentIn hz.2)
  have he := (connectedComponentIn_eq hwx).trans (connectedComponentIn_eq hwz).symm
  rw [he]
  exact mem_connectedComponentIn hz.2

theorem jordan_filled_disjoint_outside {C : Set Plane} (hC : IsSeparating C) :
    Disjoint (closure (inside C)) (outside C) := by
  rw [closure_eq_self_union_frontier, hC.frontier_inside]
  apply Set.disjoint_left.mpr
  intro z hz hout
  rcases hz with hin | hc
  · exact Set.disjoint_left.mp disjoint_inside_outside hin hout
  · exact outside_subset_compl hout hc

theorem connected_inter_outside_of_exterior_collar {C U N : Set Plane}
    (hC : IsSeparating C) (hU : IsOpen U) (hUc : IsConnected U)
    (hKU : closure (inside C) ⊆ U) (hN : IsOpen N) (hCN : C ⊆ N)
    (hNU : N ⊆ U) (hNc : IsConnected (N ∩ outside C)) :
    IsConnected (U ∩ outside C) := by
  let V := U ∩ outside C
  obtain ⟨x, hx⟩ := hNc.nonempty
  have hxV : x ∈ V := ⟨hNU hx.1, hx.2⟩
  let W := connectedComponentIn V x
  have hV : IsOpen V := hU.inter hC.isOpen_outside
  have hW : IsOpen W := hV.connectedComponentIn
  have hWV : W ⊆ V := connectedComponentIn_subset V x
  have hSW : N ∩ outside C ⊆ W := hNc.isPreconnected.subset_connectedComponentIn hx
    (fun z hz => ⟨hNU hz.1, hz.2⟩)
  let T := closure (inside C) ∪ W
  have hNT : N ⊆ T := by
    intro z hz
    by_cases hc : z ∈ C
    · exact Or.inl (frontier_subset_closure (hC.frontier_inside.symm ▸ hc))
    · have hh : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hc
      rcases hh with hi | ho
      · exact Or.inl (subset_closure hi)
      · exact Or.inr (hSW ⟨hz, ho⟩)
  have hTeq : T = inside C ∪ N ∪ W := by
    dsimp [T]
    rw [closure_eq_self_union_frontier, hC.frontier_inside]
    apply Set.Subset.antisymm
    · rintro z ((hi | hc) | hw)
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr (hCN hc))
      · exact Or.inr hw
    · rintro z ((hi | hn) | hw)
      · exact Or.inl (Or.inl hi)
      · simpa only [T, closure_eq_self_union_frontier, hC.frontier_inside] using hNT hn
      · exact Or.inr hw
  have hT : IsOpen T := by rw [hTeq]; exact (hC.isOpen_inside.union hN).union hW
  have hcl : closure T ∩ U ⊆ T := by
    intro z hz
    have hh : z ∈ closure (inside C) ∪ closure W := by
      simpa only [T, closure_union, closure_closure] using hz.1
    rcases hh with hk | hw
    · exact Or.inl hk
    · by_cases ho : z ∈ outside C
      · exact Or.inr (closure_component_inter_open_subset hV x ⟨hw, hz.2, ho⟩)
      · by_cases hc : z ∈ C
        · exact Or.inl (frontier_subset_closure (hC.frontier_inside.symm ▸ hc))
        · have hh : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hc
          exact Or.inl (subset_closure (hh.resolve_right ho))
  have hUT : U ⊆ T := hUc.isPreconnected.subset_of_closure_inter_subset hT
    ⟨x, hxV.1, Or.inr (mem_connectedComponentIn hxV)⟩ hcl
  have he : V = W := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hUT hz.1 with hk | hw
      · exact (Set.disjoint_left.mp (jordan_filled_disjoint_outside hC) hk hz.2).elim
      · exact hw
    · exact hWV
  rw [show U ∩ outside C = V from rfl, he]
  exact isConnected_connectedComponentIn_iff.mpr hxV

end RepulsiveCoulomb
