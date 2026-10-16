module

public import LeanResearch.RepulsiveCoulomb.TriangularGridCrossedEdges
public import LeanResearch.RepulsiveCoulomb.TriangleLevelSigns

@[expose] public section

/-! Exact two-crossing-edge structure of each active regular-grid triangle. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def gridTriangleNodes (i : GridTriangle) : Fin 3 → ℤ × ℤ :=
  if i.2 then ![i.1, i.1 + (1, 1), i.1 + (0, 1)]
  else ![i.1, i.1 + (1, 0), i.1 + (1, 1)]

theorem gridTriangle_crossing_iff (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) (j : Fin 3) :
    gridEdgeCrosses v t (gridTriangleEdges i j) ↔
      j ∈ triangleCrossingEdges (fun k => v (gridTriangleNodes i k)) t := by
  rw [triangleCrossingEdges_mem_iff (fun k => grid_regular_level_ne_node v ht _)]
  rcases i with ⟨⟨x, y⟩, k⟩
  cases k <;> fin_cases j <;>
    norm_num [gridEdgeCrosses, gridTriangleEdges, gridTriangleNodes, gridEdgeEnd, add_assoc] <;> tauto

def gridTriangleCrossedIndices (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (i : GridTriangle) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun j => gridEdgeCrosses v t (gridTriangleEdges i j))

theorem gridTriangleCrossedIndices_eq (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) :
    gridTriangleCrossedIndices v t i = triangleCrossingEdges (fun j => v (gridTriangleNodes i j)) t := by
  classical
  ext j
  simp only [gridTriangleCrossedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact gridTriangle_crossing_iff v ht i j

def gridTriangleCrossedEdges (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (i : GridTriangle) : Finset GridEdge :=
  (gridTriangleCrossedIndices v t i).map ⟨gridTriangleEdges i, gridTriangleEdges_injective i⟩

theorem mem_gridTriangleCrossedEdges (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ)
    (i : GridTriangle) (e : GridEdge) :
    e ∈ gridTriangleCrossedEdges v t i ↔ e ∈ range (gridTriangleEdges i) ∧ gridEdgeCrosses v t e := by
  classical
  rw [gridTriangleCrossedEdges, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨mem_range_self j, (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨⟨j, rfl⟩, hc⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩

theorem gridTriangleCrossedEdges_card (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) :
    (gridTriangleCrossedEdges v t i).card = 0 ∨ (gridTriangleCrossedEdges v t i).card = 2 := by
  rw [gridTriangleCrossedEdges, Finset.card_map, gridTriangleCrossedIndices_eq v ht i]
  exact triangleCrossingEdges_card _ _

theorem gridTriangle_other_crossed_edge (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) (i : GridTriangle) {e : GridEdge}
    (he : e ∈ gridTriangleCrossedEdges v t i) :
    ∃ f : GridEdge, f ∈ gridTriangleCrossedEdges v t i ∧ f ≠ e ∧
      ∀ g ∈ gridTriangleCrossedEdges v t i, g ≠ e → g = f := by
  classical
  let s := gridTriangleCrossedEdges v t i
  have hc : s.card = 2 := (gridTriangleCrossedEdges_card v ht i).resolve_left (by
    intro h0
    have hh : s = ∅ := Finset.card_eq_zero.mp h0
    have he' : e ∈ s := he
    rw [hh] at he'
    simpa using he')
  have hc1 : (s.erase e).card = 1 := by rw [Finset.card_erase_of_mem he, hc]
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hc1
  have hfm : f ∈ s.erase e := by rw [hf]; simp
  refine ⟨f, (Finset.mem_erase.mp hfm).2, (Finset.mem_erase.mp hfm).1, ?_⟩
  intro g hg hge
  have hgm : g ∈ s.erase e := Finset.mem_erase.mpr ⟨hge, hg⟩
  rw [hf] at hgm
  exact Finset.mem_singleton.mp hgm

end RepulsiveCoulomb
