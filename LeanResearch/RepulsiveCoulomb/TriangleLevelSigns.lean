module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

/-! The finite sign combinatorics of a triangular affine level contour. A level
avoiding vertex values crosses either zero or exactly two cyclic edges. Geometry
and mesh incidence are separate obligations. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

def triangleCrossingEdges (u : Fin 3 → ℝ) (t : ℝ) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun i => (u i < t) ≠ (u (i + 1) < t))

theorem triangleCrossingEdges_card (u : Fin 3 → ℝ) (t : ℝ) :
    (triangleCrossingEdges u t).card = 0 ∨ (triangleCrossingEdges u t).card = 2 := by
  classical
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  by_cases h0 : u 0 < t <;> by_cases h1 : u 1 < t <;> by_cases h2 : u 2 < t <;>
    norm_num [triangleCrossingEdges, hu, Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]

theorem triangleCrossingEdges_mem_iff {u : Fin 3 → ℝ} {t : ℝ}
    (ht : ∀ i, u i ≠ t) (i : Fin 3) :
    i ∈ triangleCrossingEdges u t ↔
      (u i < t ∧ t < u (i + 1)) ∨ (u (i + 1) < t ∧ t < u i) := by
  classical
  simp only [triangleCrossingEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi' : t < u i ↔ ¬ u i < t := by
    constructor
    · intro h hh; linarith
    · intro h; exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (ht _))
  have hj' : t < u (i + 1) ↔ ¬ u (i + 1) < t := by
    constructor
    · intro h hh; linarith
    · intro h; exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (ht _))
  simp only [hi', hj']
  tauto

end RepulsiveCoulomb
