import LeanResearch.RepulsiveCoulomb.TriangularGridCells

/-! Explicit regular-grid edge labels and exact two-triangle incidence. Directions
0,1,2 mean horizontal, vertical, and rising diagonal. No manifold axiom is used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

abbrev GridEdge := (ℤ × ℤ) × Fin 3
abbrev GridTriangle := (ℤ × ℤ) × Bool

def gridEdgeEnd (e : GridEdge) : ℤ × ℤ := e.1 + (![ (1, 0), (0, 1), (1, 1)] e.2)

def gridTriangleEdges (i : GridTriangle) : Fin 3 → GridEdge :=
  if i.2 then ![(i.1, 2), (i.1 + (0, 1), 0), (i.1, 1)]
  else ![(i.1, 0), (i.1 + (1, 0), 1), (i.1, 2)]

def gridEdgeTriangles (e : GridEdge) : Fin 2 → GridTriangle :=
  (![ ![(e.1, false), (e.1 - (0, 1), true)],
      ![(e.1, true), (e.1 - (1, 0), false)],
      ![(e.1, false), (e.1, true)] ] e.2)

theorem gridTriangleEdges_injective (i : GridTriangle) : Function.Injective (gridTriangleEdges i) := by
  rcases i with ⟨b, k⟩
  intro j l h
  have hh := congrArg Prod.snd h
  cases k <;> fin_cases j <;> fin_cases l <;> simp_all [gridTriangleEdges]

theorem gridEdgeTriangles_injective (e : GridEdge) : Function.Injective (gridEdgeTriangles e) := by
  rcases e with ⟨b, d⟩
  intro j l h
  have hh := congrArg Prod.snd h
  fin_cases d <;> fin_cases j <;> fin_cases l <;> simp_all [gridEdgeTriangles]

theorem grid_triangle_edge_incidence (i : GridTriangle) (e : GridEdge) :
    e ∈ range (gridTriangleEdges i) ↔
      i = gridEdgeTriangles e 0 ∨ i = gridEdgeTriangles e 1 := by
  rcases i with ⟨b, k⟩
  rcases e with ⟨c, d⟩
  cases k <;> fin_cases d <;>
    simp [gridTriangleEdges, gridEdgeTriangles, Fin.exists_fin_succ, eq_sub_iff_add_eq,
      or_comm, eq_comm]

theorem gridEdgeTriangles_incident (e : GridEdge) (j : Fin 2) :
    e ∈ range (gridTriangleEdges (gridEdgeTriangles e j)) := by
  rw [grid_triangle_edge_incidence]
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gridEdgeTriangles_common_edge (e f : GridEdge)
    (h0 : f ∈ range (gridTriangleEdges (gridEdgeTriangles e 0)))
    (h1 : f ∈ range (gridTriangleEdges (gridEdgeTriangles e 1))) : e = f := by
  rw [grid_triangle_edge_incidence] at h0 h1
  rcases e with ⟨⟨x, y⟩, d⟩
  rcases f with ⟨⟨u, v⟩, k⟩
  fin_cases d <;> fin_cases k <;>
    norm_num [gridEdgeTriangles, Prod.mk.injEq] at h0 h1 ⊢ <;> omega

end RepulsiveCoulomb
