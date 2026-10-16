module

public import LeanResearch.RepulsiveCoulomb.FiniteNestedPolygonExterior

@[expose] public section

/-! Local connected exterior for finite polygon families whose filled interiors
are contained in the prescribed connected open set. Nesting is allowed. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem finite_disjoint_polygon_local_exterior_connected {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι) {U : Set Plane}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hsub : ∀ i ∈ s, closure (inside (P i).carrier) ⊆ U)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => closure (inside (P i).carrier))) :
    IsConnected (U ∩ ⋂ i ∈ s, outside (P i).carrier) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hUc
  | @insert i s hi ih =>
    have hds : (s : Set ι).Pairwise (Disjoint on fun i => closure (inside (P i).carrier)) :=
      hdis.mono (by intro j hj; exact Finset.mem_insert_of_mem hj)
    have hconn := ih (fun j hj => hsub j (Finset.mem_insert_of_mem hj)) hds
    have hopen : IsOpen (U ∩ ⋂ j ∈ s, outside (P j).carrier) :=
      hU.inter (isOpen_biInter_finset (fun j _ => (P j).isSeparating_carrier.isOpen_outside))
    have hKi : closure (inside (P i).carrier) ⊆ U ∩ ⋂ j ∈ s, outside (P j).carrier := by
      intro z hz
      refine ⟨hsub i (Finset.mem_insert_self i s) hz, ?_⟩
      simp only [mem_iInter]
      intro j hj
      rw [← jordan_compl_filled_eq_outside (P j).isSeparating_carrier]
      intro hzj
      have hij : i ≠ j := by intro he; subst j; exact hi hj
      exact Set.disjoint_left.mp (hdis (Finset.mem_insert_self i s)
        (Finset.mem_insert_of_mem hj) hij) hz hzj
    have hc := polygon_connected_inter_outside (P i) hopen hconn hKi
    simpa only [Finset.set_biInter_insert, inter_assoc, inter_left_comm, inter_comm] using hc

theorem finite_polygon_local_exterior_connected {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι) {U : Set Plane}
    (hU : IsOpen U) (hUc : IsConnected U)
    (hsub : ∀ i ∈ s, closure (inside (P i).carrier) ⊆ U)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => (P i).carrier)) :
    IsConnected (U ∩ ⋂ i ∈ s, outside (P i).carrier) := by
  classical
  let K : ι → Set Plane := fun i => closure (inside (P i).carrier)
  let M := s.filter (fun i => MaximalFor (· ∈ s) K i)
  have hM : (M : Set ι).Pairwise (Disjoint on K) := by
    intro i hi j hj hij
    obtain ⟨his,hmaxi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs,hmaxj⟩ := Finset.mem_filter.mp hj
    rcases jordan_disjoint_filled_trichotomy (P i).isSeparating_carrier
      (P j).isSeparating_carrier (hdis his hjs hij) with h | h | h
    · have hji : K j ⊆ K i := hmaxi.2 hjs (h.trans subset_closure)
      obtain ⟨z,hz⟩ := (P j).isSeparating_carrier.isJordanCurve.nonempty
      have hzK : z ∈ K j := frontier_subset_closure
        ((P j).isSeparating_carrier.frontier_inside.symm ▸ hz)
      exact (inside_subset_compl (h (hji hzK)) hz).elim
    · have hij' : K i ⊆ K j := hmaxj.2 his (h.trans subset_closure)
      obtain ⟨z,hz⟩ := (P i).isSeparating_carrier.isJordanCurve.nonempty
      have hzK : z ∈ K i := frontier_subset_closure
        ((P i).isSeparating_carrier.frontier_inside.symm ▸ hz)
      exact (inside_subset_compl (h (hij' hzK)) hz).elim
    · exact h
  have heq : (⋂ i ∈ s, outside (P i).carrier) = ⋂ i ∈ M, outside (P i).carrier := by
    ext z
    simp only [mem_iInter]
    constructor
    · intro hz i hi
      exact hz i (Finset.mem_filter.mp hi).1
    · intro hz i hi
      obtain ⟨j,hij,hj⟩ := finset_exists_maximalFor_above s K hi
      have hjM : j ∈ M := Finset.mem_filter.mpr ⟨hj.1,hj⟩
      have hzj := hz j hjM
      rw [← jordan_compl_filled_eq_outside (P j).isSeparating_carrier] at hzj
      rw [← jordan_compl_filled_eq_outside (P i).isSeparating_carrier]
      exact fun hzi => hzj (hij hzi)
  rw [heq]
  exact finite_disjoint_polygon_local_exterior_connected n P M hU hUc
    (fun i hi => hsub i (Finset.mem_filter.mp hi).1) hM

end RepulsiveCoulomb
