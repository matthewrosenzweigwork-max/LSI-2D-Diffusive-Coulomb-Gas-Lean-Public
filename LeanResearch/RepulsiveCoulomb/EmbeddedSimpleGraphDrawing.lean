import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.Graph.CycleJordan
import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.Graph.Maps

/-! A straight-line drawing of an injectively embedded simple graph, derived from
explicit vertex exclusion and edge intersection estimates. Edge labels remain Sym2. -/
noncomputable section
open Set Schoenflies
namespace RepulsiveCoulomb

variable {V : Type*}

def embeddedSimpleGraph (G : SimpleGraph V) (p : V → Plane) : Graph Plane (Sym2 V) :=
  (Graph.ofSimpleGraph G).map p

def embeddedSimpleDrawing (p : V → Plane) (e : Sym2 V) : ℝ → Plane :=
  AffineMap.lineMap (p e.out.1) (p e.out.2)

theorem sym2_out_pair (e : Sym2 V) : s(e.out.1, e.out.2) = e := by
  rw [Sym2.mk, e.out_eq]

theorem embeddedSimpleGraph_link (G : SimpleGraph V) (p : V → Plane) {a b : V}
    (h : G.Adj a b) : (embeddedSimpleGraph G p).IsLink s(a,b) (p a) (p b) := by
  exact Graph.IsLink.map p (G := Graph.ofSimpleGraph G) ⟨rfl, h⟩

theorem embeddedSimpleGraph_vertex (G : SimpleGraph V) (p : V → Plane) (a : V) :
    p a ∈ (embeddedSimpleGraph G p).vertexSet := by
  exact mem_image_of_mem p (mem_univ a)

theorem embeddedSimpleDrawing_arc (p : V → Plane) {e : Sym2 V} {a b : V}
    (he : e = s(a,b)) : Graph.edgeArc (embeddedSimpleDrawing p) e = segment ℝ (p a) (p b) := by
  change (AffineMap.lineMap (p e.out.1) (p e.out.2)) '' unitInterval = _
  rw [← segment_eq_image_lineMap]
  rcases Sym2.eq_iff.mp ((sym2_out_pair e).trans he) with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb,segment_symm]

theorem embeddedSimpleGraph_isDrawing (G : SimpleGraph V) (p : V → Plane)
    (hp : Function.Injective p)
    (hvertex : ∀ a b e, G.Adj a b → p e ∈ segment ℝ (p a) (p b) → e = a ∨ e = b)
    (hinter : ∀ a b c d, G.Adj a b → G.Adj c d → ∀ z,
      z ∈ segment ℝ (p a) (p b) → z ∈ segment ℝ (p c) (p d) →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨
        ∃ e, z = p e ∧ (e = a ∨ e = b) ∧ (e = c ∨ e = d)) :
    Graph.IsDrawing (embeddedSimpleGraph G p) (embeddedSimpleDrawing p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have hadj : G.Adj e.out.1 e.out.2 := by
      change e ∈ G.edgeSet at he
      rw [← sym2_out_pair e] at he
      exact he
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap (hp.ne hadj.ne), ?_⟩
    simp only [embeddedSimpleDrawing, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    have hlink := embeddedSimpleGraph_link G p hadj
    rw [sym2_out_pair e] at hlink
    exact hlink
  · intro e x y w hl hw hew
    change ∃ a b, (Graph.ofSimpleGraph G).IsLink e a b ∧ p a = x ∧ p b = y at hl
    obtain ⟨a,b,hl,rfl,rfl⟩ := hl
    have hab : G.Adj a b := by
      have hm := hl.2
      rw [hl.1] at hm
      exact hm
    change w ∈ p '' univ at hw
    obtain ⟨q,_,rfl⟩ := hw
    rw [embeddedSimpleDrawing_arc p hl.1] at hew
    exact (hvertex a b q hab hew).imp (congrArg p) (congrArg p)
  · intro e f he hf hef z hze hzf
    have heq := sym2_out_pair e
    have hfq := sym2_out_pair f
    have ha : G.Adj e.out.1 e.out.2 := by
      change e ∈ G.edgeSet at he
      rw [← heq] at he
      exact he
    have hb : G.Adj f.out.1 f.out.2 := by
      change f ∈ G.edgeSet at hf
      rw [← hfq] at hf
      exact hf
    rw [embeddedSimpleDrawing_arc p heq.symm] at hze
    rw [embeddedSimpleDrawing_arc p hfq.symm] at hzf
    rcases hinter _ _ _ _ ha hb z hze hzf with h | h | ⟨q,rfl,hqe,hqf⟩
    · exact (hef (heq.symm.trans ((congrArg₂ (fun a b => s(a,b)) h.1 h.2).trans hfq))).elim
    · have heff : e = f := by
        rw [← heq, ← hfq, h.1, h.2, Sym2.eq_swap]
      exact (hef heff).elim
    · refine ⟨embeddedSimpleGraph_vertex G p q, ?_, ?_⟩
      · have hlink := embeddedSimpleGraph_link G p ha
        rw [heq] at hlink
        rcases hqe with rfl | rfl
        · exact ⟨_, hlink⟩
        · exact ⟨_, hlink.symm⟩
      · have hlink := embeddedSimpleGraph_link G p hb
        rw [hfq] at hlink
        rcases hqf with rfl | rfl
        · exact ⟨_, hlink⟩
        · exact ⟨_, hlink.symm⟩

end RepulsiveCoulomb
