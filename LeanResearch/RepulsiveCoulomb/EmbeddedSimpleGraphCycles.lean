module

public import LeanResearch.RepulsiveCoulomb.EmbeddedSimpleGraphDrawing
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

/-! Exact edge-list-preserving transport from simple graph paths and cycles to
the approved geometric graph API. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb
variable {V : Type*}

theorem embedded_walkVertices_support (G : SimpleGraph V) (p : V → Plane)
    (hp : Function.Injective p) {a b x : V} (w : G.Walk a b)
    (hx : p x ∈ (embeddedSimpleGraph G p).walkVertices (p a) w.edges) : x ∈ w.support := by
  rw [Graph.mem_walkVertices_iff] at hx
  rcases hx with hx | ⟨e, he, hinc⟩
  · have hxa := hp hx
    subst x
    exact w.start_mem_support
  · change ((Graph.ofSimpleGraph G).map p).Inc e (p x) at hinc
    obtain ⟨q, hq, heq⟩ := (Graph.map_inc p).mp hinc
    have hxq := hp heq
    subst q
    obtain ⟨y, hxy⟩ := hq
    have hexy : e = s(x,y) := hxy.1
    rw [hexy] at he
    exact w.fst_mem_support_of_mem_edges he

theorem embeddedSimpleGraph_path (G : SimpleGraph V) (p : V → Plane)
    (hp : Function.Injective p) {a b : V} (w : G.Walk a b) (hw : w.IsPath) :
    (embeddedSimpleGraph G p).IsPath (p a) w.edges (p b) := by
  induction w with
  | nil => exact .nil (embeddedSimpleGraph_vertex G p _)
  | @cons a c b hac w ih =>
    have hh := (SimpleGraph.Walk.cons_isPath_iff hac w).mp hw
    exact .cons (embeddedSimpleGraph_link G p hac) (ih hh.1)
      (fun hx => hh.2 (embedded_walkVertices_support G p hp w hx))

theorem embeddedSimpleGraph_cycle_jordan (G : SimpleGraph V) (p : V → Plane)
    (hp : Function.Injective p)
    (hd : Graph.IsDrawing (embeddedSimpleGraph G p) (embeddedSimpleDrawing p))
    {a : V} (w : G.Walk a a) (hw : w.IsCycle) :
    IsJordanCurve (Graph.edgesCover (embeddedSimpleDrawing p) w.edges) := by
  cases w with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hw).elim
  | @cons a b a hab w =>
    have hh := (SimpleGraph.Walk.cons_isCycle_iff w hab).mp hw
    apply hd.cycle_isJordanCurve
    exact ⟨(embeddedSimpleGraph_link G p hab).symm,
      embeddedSimpleGraph_path G p hp w hh.1, hh.2⟩

end RepulsiveCoulomb
