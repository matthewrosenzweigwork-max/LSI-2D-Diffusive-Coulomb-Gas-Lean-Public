module

public import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.CrosscutCells

@[expose] public section

/-! Pairwise nesting of actual Jordan regions. Uses the approved Jordan separation
and absorption theorems, not a newly assumed finite-family exterior property. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem jordan_outside_mono_of_curve_subset_inside {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D) (hCD : C ⊆ inside D) :
    outside D ⊆ outside C := by
  have hd : Disjoint (outside D) C := by
    apply Set.disjoint_left.mpr
    intro z hz hzC
    exact Set.disjoint_left.mp disjoint_inside_outside (hCD hzC) hz
  obtain ⟨W, V, hWV, hsub⟩ := hC.exists_isRegionPair_subset
    hD.isConnected_outside.isPreconnected hD.isConnected_outside.nonempty hd
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hD.not_isBounded_outside (hC.isBounded_inside.subset hsub)).elim
  · exact hsub

theorem jordan_inside_mono_of_curve_subset_inside {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D) (hCD : C ⊆ inside D) :
    inside C ⊆ inside D := by
  have ho := jordan_outside_mono_of_curve_subset_inside hC hD hCD
  have hDC : D ⊆ outside C := by
    intro z hz
    apply hD.absorption hC (Or.inr rfl) (Or.inr rfl) ho
    refine ⟨hz, ?_⟩
    intro hzC
    exact inside_subset_compl (hCD hzC) hz
  intro z hz
  have hzD : z ∉ D := fun hd => Set.disjoint_left.mp disjoint_inside_outside hz (hDC hd)
  have hh : z ∈ inside D ∪ outside D := by rw [inside_union_outside]; exact hzD
  exact hh.resolve_right (fun hout => Set.disjoint_left.mp disjoint_inside_outside hz (ho hout))

theorem jordan_inside_disjoint_of_curves_outside {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D)
    (hCD : C ⊆ outside D) (hDC : D ⊆ outside C) :
    Disjoint (inside C) (inside D) := by
  have hd : Disjoint (inside C) D := by
    apply Set.disjoint_left.mpr
    intro z hz hzD
    exact Set.disjoint_left.mp disjoint_inside_outside hz (hDC hzD)
  obtain ⟨W, V, hWV, hsub⟩ := hD.exists_isRegionPair_subset
    hC.isConnected_inside.isPreconnected hC.isConnected_inside.nonempty hd
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hb := hC.absorption hD (Or.inl rfl) (Or.inl rfl) hsub
    obtain ⟨z, hz⟩ := hC.isJordanCurve.nonempty
    have hzD : z ∉ D := outside_subset_compl (hCD hz)
    exact (Set.disjoint_left.mp disjoint_inside_outside (hb ⟨hz, hzD⟩) (hCD hz)).elim
  · exact disjoint_inside_outside.symm.mono_left hsub

end RepulsiveCoulomb
