module

public import LeanResearch.RepulsiveCoulomb.JordanRegionNesting

@[expose] public section

/-! Disjoint Jordan curves have nested filled interiors or disjoint filled
interiors. This supplies pairwise topology, not finite-family exterior connectivity. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

theorem jordan_curve_region_dichotomy {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D) (hdis : Disjoint C D) :
    C ⊆ inside D ∨ C ⊆ outside D := by
  obtain ⟨W, V, hWV, hsub⟩ := hD.exists_isRegionPair_subset
    hC.isJordanCurve.isConnected.isPreconnected hC.isJordanCurve.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hsub
  · exact Or.inr hsub

theorem jordan_filled_inside_subset_of_curve_subset {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D) (hCD : C ⊆ inside D) :
    closure (inside C) ⊆ inside D := by
  rw [closure_eq_self_union_frontier, hC.frontier_inside]
  exact union_subset (jordan_inside_mono_of_curve_subset_inside hC hD hCD) hCD

theorem jordan_filled_inside_disjoint_of_curves_outside {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D) (hdis : Disjoint C D)
    (hCD : C ⊆ outside D) (hDC : D ⊆ outside C) :
    Disjoint (closure (inside C)) (closure (inside D)) := by
  rw [closure_eq_self_union_frontier, closure_eq_self_union_frontier,
    hC.frontier_inside, hD.frontier_inside]
  have hii := jordan_inside_disjoint_of_curves_outside hC hD hCD hDC
  apply Set.disjoint_left.mpr
  intro z hzC hzD
  rcases hzC with hiC | hc
  · rcases hzD with hiD | hd
    · exact Set.disjoint_left.mp hii hiC hiD
    · exact Set.disjoint_left.mp disjoint_inside_outside hiC (hDC hd)
  · rcases hzD with hiD | hd
    · exact Set.disjoint_left.mp disjoint_inside_outside hiD (hCD hc)
    · exact Set.disjoint_left.mp hdis hc hd

theorem jordan_disjoint_filled_trichotomy {C D : Set Plane}
    (hC : IsSeparating C) (hD : IsSeparating D) (hdis : Disjoint C D) :
    closure (inside C) ⊆ inside D ∨ closure (inside D) ⊆ inside C ∨
      Disjoint (closure (inside C)) (closure (inside D)) := by
  rcases jordan_curve_region_dichotomy hC hD hdis with hc | hc
  · exact Or.inl (jordan_filled_inside_subset_of_curve_subset hC hD hc)
  · rcases jordan_curve_region_dichotomy hD hC hdis.symm with hd | hd
    · exact Or.inr (Or.inl (jordan_filled_inside_subset_of_curve_subset hD hC hd))
    · exact Or.inr (Or.inr (jordan_filled_inside_disjoint_of_curves_outside hC hD hdis hc hd))

end RepulsiveCoulomb
