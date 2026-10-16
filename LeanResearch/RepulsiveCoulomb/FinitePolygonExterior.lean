import LeanResearch.RepulsiveCoulomb.PolygonExteriorCollar

/-! Connected exterior of finitely many disjoint filled polygons. This is an
actual finite-family topological consequence of the approved polygon collars. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem jordan_compl_filled_eq_outside {C : Set Plane} (hC : IsSeparating C) :
    (closure (inside C))ᶜ = outside C := by
  rw [closure_eq_self_union_frontier, hC.frontier_inside]
  ext z
  constructor
  · intro hz
    have hc : z ∉ C := fun h => hz (Or.inr h)
    have hi : z ∉ inside C := fun h => hz (Or.inl h)
    have hh : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hc
    exact hh.resolve_left hi
  · intro hz hi
    rcases hi with hi | hc
    · exact Set.disjoint_left.mp disjoint_inside_outside hi hz
    · exact outside_subset_compl hz hc

theorem finite_disjoint_polygon_exterior_connected {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => closure (inside (P i).carrier))) :
    IsConnected (⋂ i ∈ s, outside (P i).carrier) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isConnected_univ : IsConnected (univ : Set Plane))
  | @insert i s hi ih =>
    have hds : (s : Set ι).Pairwise (Disjoint on fun i => closure (inside (P i).carrier)) :=
      hdis.mono (by intro j hj; exact Finset.mem_insert_of_mem hj)
    have hconn := ih hds
    have hopen : IsOpen (⋂ j ∈ s, outside (P j).carrier) :=
      isOpen_biInter_finset (fun j _ => (P j).isSeparating_carrier.isOpen_outside)
    have hsub : closure (inside (P i).carrier) ⊆ ⋂ j ∈ s, outside (P j).carrier := by
      intro z hz
      simp only [mem_iInter]
      intro j hj
      rw [← jordan_compl_filled_eq_outside (P j).isSeparating_carrier]
      intro hzj
      have hij : i ≠ j := by intro he; subst j; exact hi hj
      exact Set.disjoint_left.mp (hdis (Finset.mem_insert_self i s)
        (Finset.mem_insert_of_mem hj) hij) hz hzj
    have hc := polygon_connected_inter_outside (P i) hopen hconn hsub
    simpa only [Finset.set_biInter_insert, inter_comm] using hc

end RepulsiveCoulomb
