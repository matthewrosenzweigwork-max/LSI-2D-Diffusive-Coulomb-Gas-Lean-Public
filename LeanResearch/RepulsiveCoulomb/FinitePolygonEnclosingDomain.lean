import LeanResearch.RepulsiveCoulomb.FinitePolygonLocalExterior

/-! Select the innermost polygon enclosing a connected observation set, if one
exists. This avoids the false assumption that the global exterior meets that set. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem finite_polygon_enclosing_domain {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι) {B : Set Plane}
    (hB : IsConnected B)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => (P i).carrier)) :
    ∃ U : Set Plane, ∃ D : Finset ι,
      IsOpen U ∧ IsConnected U ∧ B ⊆ U ∧ D ⊆ s ∧
      (∀ i ∈ D, closure (inside (P i).carrier) ⊆ U) ∧
      (∀ i ∈ s, ((P i).carrier ∩ U).Nonempty → i ∈ D) ∧
      (∀ i ∈ D, Disjoint B (P i).carrier → B ⊆ outside (P i).carrier) := by
  classical
  let K : ι → Set Plane := fun i => closure (inside (P i).carrier)
  let A := s.filter (fun i => B ⊆ inside (P i).carrier)
  by_cases hA : A.Nonempty
  · obtain ⟨k,hk⟩ := A.exists_minimalFor K hA
    have hks := (Finset.mem_filter.mp hk.1).1
    have hBk := (Finset.mem_filter.mp hk.1).2
    let D := s.filter (fun i => K i ⊆ inside (P k).carrier)
    refine ⟨inside (P k).carrier, D, (P k).isSeparating_carrier.isOpen_inside,
      (P k).isSeparating_carrier.isConnected_inside, hBk, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi hmeet
      have hik : i ≠ k := by
        intro h
        subst i
        obtain ⟨z,hzC,hzI⟩ := hmeet
        exact inside_subset_compl hzI hzC
      have hd := hdis hi hks hik
      rcases jordan_curve_region_dichotomy (P i).isSeparating_carrier
        (P k).isSeparating_carrier hd with hinside | hout
      · exact Finset.mem_filter.mpr ⟨hi,
          jordan_filled_inside_subset_of_curve_subset (P i).isSeparating_carrier
            (P k).isSeparating_carrier hinside⟩
      · obtain ⟨z,hzC,hzI⟩ := hmeet
        exact (Set.disjoint_left.mp disjoint_inside_outside hzI (hout hzC)).elim
    · intro i hi hd
      rcases jordan_connected_region_dichotomy (P i).isSeparating_carrier hB hd with hinside | hout
      · have hiA : i ∈ A := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hinside⟩
        have hiK : K i ⊆ inside (P k).carrier := (Finset.mem_filter.mp hi).2
        have hki : K k ⊆ K i := hk.2 hiA (hiK.trans subset_closure)
        obtain ⟨z,hz⟩ := (P k).isSeparating_carrier.isJordanCurve.nonempty
        have hzK : z ∈ K k := frontier_subset_closure
          ((P k).isSeparating_carrier.frontier_inside.symm ▸ hz)
        exact (inside_subset_compl (hiK (hki hzK)) hz).elim
      · exact hout
  · refine ⟨univ,s,isOpen_univ,isConnected_univ,subset_univ _,Finset.Subset.refl _,?_,?_,?_⟩
    · intro i _
      exact subset_univ _
    · intro i hi _
      exact hi
    · intro i hi hd
      rcases jordan_connected_region_dichotomy (P i).isSeparating_carrier hB hd with hinside | hout
      · exact (hA ⟨i,Finset.mem_filter.mpr ⟨hi,hinside⟩⟩).elim
      · exact hout

end RepulsiveCoulomb
