module

public import LeanResearch.RepulsiveCoulomb.TriangularGridIncidence
public import LeanResearch.RepulsiveCoulomb.TriangularGridContourSegments

@[expose] public section

/-! A genuine finite set of crossed lattice edges and their actual physical
crossing points. Finiteness follows from finite nodal support, not an assumption. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

def gridEdgeCrosses (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridEdge) : Prop :=
  (v e.1 < t ∧ t < v (gridEdgeEnd e)) ∨ (v (gridEdgeEnd e) < t ∧ t < v e.1)

def gridActiveEdges (v : (ℤ × ℤ) →₀ ℝ) : Finset GridEdge := by
  classical
  let s : Finset GridEdge := v.support.product Finset.univ
  exact s ∪ s.image (fun e => (e.1 - (![ (1, 0), (0, 1), (1, 1)] e.2), e.2))

theorem gridEdgeCrosses_active (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridEdge)
    (he : gridEdgeCrosses v t e) : e ∈ gridActiveEdges v := by
  classical
  by_cases h0 : v e.1 = 0
  · have h1 : v (gridEdgeEnd e) ≠ 0 := by
      intro h1
      rcases he with h | h <;> rw [h0, h1] at h <;> linarith [h.1, h.2]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(gridEdgeEnd e, e.2), Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr h1, Finset.mem_univ _⟩, ?_⟩
    apply Prod.ext
    · change e.1 + _ - _ = e.1
      exact add_sub_cancel_right _ _
    · rfl
  · exact Finset.mem_union_left _ (Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr h0, Finset.mem_univ _⟩)

def gridCrossedEdges (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) : Finset GridEdge := by
  classical
  exact (gridActiveEdges v).filter (gridEdgeCrosses v t)

theorem mem_gridCrossedEdges (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridEdge) :
    e ∈ gridCrossedEdges v t ↔ gridEdgeCrosses v t e := by
  classical
  change e ∈ (gridActiveEdges v).filter (gridEdgeCrosses v t) ↔ _
  rw [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨gridEdgeCrosses_active v t e h, h⟩⟩

theorem complexLatticePoint_injective : Function.Injective complexLatticePoint := by
  intro p q h
  apply Prod.ext
  · have hh := congrArg Complex.re h
    change (p.1 : ℝ) = (q.1 : ℝ) at hh
    exact_mod_cast hh
  · have hh := congrArg Complex.im h
    change (p.2 : ℝ) = (q.2 : ℝ) at hh
    exact_mod_cast hh

theorem gridEdge_start_ne_end (e : GridEdge) : e.1 ≠ gridEdgeEnd e := by
  rcases e with ⟨⟨x, y⟩, d⟩
  intro h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  fin_cases d <;> norm_num [gridEdgeEnd] at h0 <;> norm_num [gridEdgeEnd] at h1 <;> omega

def gridEdgeLevelPoint (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridEdge) : ℂ :=
  affineLevelEdgePoint (complexLatticePoint e.1) (complexLatticePoint (gridEdgeEnd e))
    (v e.1) (v (gridEdgeEnd e)) t

theorem gridEdgeLevelPoint_mem_openSegment (v : (ℤ × ℤ) →₀ ℝ) (t : ℝ) (e : GridEdge)
    (he : e ∈ gridCrossedEdges v t) :
    gridEdgeLevelPoint v t e ∈ openSegment ℝ (complexLatticePoint e.1)
      (complexLatticePoint (gridEdgeEnd e)) :=
  affineLevelEdgePoint_mem_openSegment _ _ ((mem_gridCrossedEdges v t e).mp he)

end RepulsiveCoulomb
