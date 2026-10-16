module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Tactic

@[expose] public section

/-! A finite family of empty sets or genuine segments has an actual finite
nondegenerate segment representation, with exact union equality. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem finite_union_empty_or_segments {ι : Type*} (s : Finset ι) (F : ι → Set ℂ)
    (hF : ∀ i ∈ s, F i = ∅ ∨ ∃ p q : ℂ, p ≠ q ∧ F i = segment ℝ p q) :
    ∃ T : Finset (ℂ × ℂ), (∀ e ∈ T, e.1 ≠ e.2) ∧
      (⋃ i ∈ s, F i) = ⋃ e ∈ T, segment ℝ e.1 e.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨T, hT, heq⟩ := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    rcases hF i (Finset.mem_insert_self _ _) with hzero | ⟨p, q, hpq, hs⟩
    · refine ⟨T, hT, ?_⟩
      simpa only [Finset.set_biUnion_insert, hzero, empty_union] using heq
    · refine ⟨insert (p, q) T, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hpq
        · exact hT e he
      · simp only [Finset.set_biUnion_insert, hs, heq]

end RepulsiveCoulomb
