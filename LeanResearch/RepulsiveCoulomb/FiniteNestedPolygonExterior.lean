module

public import LeanResearch.RepulsiveCoulomb.FinitePolygonExterior
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-! Removing nesting by actual finite maximal selection. The common exterior of
any finite family of pairwise disjoint polygonal Jordan curves is connected. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem finset_exists_maximalFor_above {ι α : Type*} [Preorder α]
    (s : Finset ι) (f : ι → α) {i : ι} (hi : i ∈ s) :
    ∃ j, f i ≤ f j ∧ MaximalFor (· ∈ s) f j := by
  classical
  let t := s.filter (fun j => f i ≤ f j)
  obtain ⟨j, hj⟩ := t.exists_maximalFor f ⟨i, Finset.mem_filter.mpr ⟨hi, le_rfl⟩⟩
  have hj' := Finset.mem_filter.mp hj.1
  refine ⟨j, hj'.2, hj'.1, ?_⟩
  intro k hk hjk
  exact hj.2 (Finset.mem_filter.mpr ⟨hk, hj'.2.trans hjk⟩) hjk

theorem finite_polygon_exterior_connected {ι : Type*} (n : ι → ℕ)
    (P : ∀ i, ClosedPolygon (n i)) (s : Finset ι)
    (hdis : (s : Set ι).Pairwise (Disjoint on fun i => (P i).carrier)) :
    IsConnected (⋂ i ∈ s, outside (P i).carrier) := by
  classical
  let K : ι → Set Plane := fun i => closure (inside (P i).carrier)
  let M := s.filter (fun i => MaximalFor (· ∈ s) K i)
  have hM : (M : Set ι).Pairwise (Disjoint on K) := by
    intro i hi j hj hij
    obtain ⟨his, hmaxi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, hmaxj⟩ := Finset.mem_filter.mp hj
    rcases jordan_disjoint_filled_trichotomy (P i).isSeparating_carrier
      (P j).isSeparating_carrier (hdis his hjs hij) with h | h | h
    · have hji : K j ⊆ K i := hmaxi.2 hjs (h.trans subset_closure)
      obtain ⟨z, hz⟩ := (P j).isSeparating_carrier.isJordanCurve.nonempty
      have hzK : z ∈ K j := frontier_subset_closure
        ((P j).isSeparating_carrier.frontier_inside.symm ▸ hz)
      exact (inside_subset_compl (h (hji hzK)) hz).elim
    · have hij' : K i ⊆ K j := hmaxj.2 his (h.trans subset_closure)
      obtain ⟨z, hz⟩ := (P i).isSeparating_carrier.isJordanCurve.nonempty
      have hzK : z ∈ K i := frontier_subset_closure
        ((P i).isSeparating_carrier.frontier_inside.symm ▸ hz)
      exact (inside_subset_compl (h (hij' hzK)) hz).elim
    · exact h
  have heq : (⋂ i ∈ s, outside (P i).carrier) = ⋂ i ∈ M, outside (P i).carrier := by
    ext z
    simp only [mem_iInter]
    constructor
    · intro hz i hi
      exact hz i (Finset.mem_filter.mp hi).1
    · intro hz i hi
      obtain ⟨j, hij, hj⟩ := finset_exists_maximalFor_above s K hi
      have hjM : j ∈ M := Finset.mem_filter.mpr ⟨hj.1, hj⟩
      have hzj := hz j hjM
      rw [← jordan_compl_filled_eq_outside (P j).isSeparating_carrier] at hzj
      rw [← jordan_compl_filled_eq_outside (P i).isSeparating_carrier]
      exact fun hzi => hzj (hij hzi)
  rw [heq]
  exact finite_disjoint_polygon_exterior_connected n P M hM

end RepulsiveCoulomb
