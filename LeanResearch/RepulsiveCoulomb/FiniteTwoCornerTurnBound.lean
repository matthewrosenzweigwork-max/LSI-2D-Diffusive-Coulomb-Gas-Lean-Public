module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! The strict two-corner budget used at the final actual bigon exclusion.
Physical vertex injectivity allows at most one exceptional corner at each
of the two original endpoints. All remaining turns are nonpositive. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finite_sum_lt_two_pi_of_two_exceptional_vertices
    {ι X : Type*} (s : Finset ι) (vertex : ι → X) (turn : ι → ℝ)
    (hvertex : Set.InjOn vertex (s : Set ι)) {p q : X} (hpq : p ≠ q)
    (hstrict : ∀ i ∈ s, turn i < Real.pi)
    (hnonpos : ∀ i ∈ s, vertex i ≠ p → vertex i ≠ q → turn i ≤ 0) :
    (∑ i ∈ s, turn i) < 2 * Real.pi := by
  classical
  let t := s.filter (fun i => vertex i = p ∨ vertex i = q)
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hsum : (∑ i ∈ s, turn i) ≤ ∑ i ∈ t, turn i := by
    apply Finset.sum_le_sum_of_subset_of_nonpos hsub
    intro i hi hit
    have hnot : ¬ (vertex i = p ∨ vertex i = q) := by
      intro he
      exact hit (Finset.mem_filter.mpr ⟨hi, he⟩)
    exact hnonpos i hi (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))
  have hcard : t.card ≤ 2 := by
    have he := Finset.card_le_card_of_injOn (s := t) (t := {p, q}) vertex
      (by
        intro i hi
        simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using
          (Finset.mem_filter.mp hi).2)
      (fun i hi j hj he => hvertex (hsub hi) (hsub hj) he)
    simpa [hpq] using he
  by_cases hne : t.Nonempty
  · have hs := Finset.sum_lt_sum_of_nonempty hne (fun i hi => hstrict i (hsub hi))
    have hb : (∑ i ∈ t, Real.pi) ≤ 2 * Real.pi := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) Real.pi_pos.le
    exact hsum.trans_lt (hs.trans_le hb)
  · have ht : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [ht, Finset.sum_empty] at hsum
    exact hsum.trans_lt (by positivity)

end RepulsiveCoulomb
