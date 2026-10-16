module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

@[expose] public section

/-! Exact complete-graph triple incidence counts. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb
variable {α : Type*} [Fintype α] [DecidableEq α]

def tripleSupersets (s : Finset α) : Finset (Finset α) :=
  (Finset.univ.powersetCard 3).filter (s ⊆ ·)

theorem tripleSupersets_card_two {s : Finset α} (hs : s.card = 2) :
    (tripleSupersets s).card = Fintype.card α - 2 := by
  rw [tripleSupersets, Finset.card_filter_powersetCard_subset s Finset.univ 3
    (Finset.subset_univ s) (by omega), hs]
  simp

theorem two_subsets_union_card_three {s t : Finset α} (hs : s.card = 2) (ht : t.card = 2)
    (hne : s ≠ t) (hd : ¬ Disjoint s t) : (s ∪ t).card = 3 := by
  have hpos : 0 < (s ∩ t).card :=
    Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hd)
  have hu := Finset.card_union_add_card_inter s t
  rw [hs, ht] at hu
  have hlow : 2 ≤ (s ∪ t).card := by simpa only [hs] using Finset.card_le_card (Finset.subset_union_left : s ⊆ s ∪ t)
  have hnot : (s ∪ t).card ≠ 2 := by
    intro h
    have hsU : s = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have htU : t = s ∪ t := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    exact hne (hsU.trans htU.symm)
  omega

theorem tripleSupersets_card_four {s : Finset α} (hs : s.card = 4) :
    (tripleSupersets s).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨htr, hsub⟩ := Finset.mem_filter.mp ht
  have htc := (Finset.mem_powersetCard.mp htr).2
  have hh := Finset.card_le_card hsub
  omega

theorem tripleSupersets_card_three {s : Finset α} (hs : s.card = 3) :
    (tripleSupersets s).card = 1 := by
  rw [tripleSupersets, Finset.card_filter_powersetCard_subset s Finset.univ 3
    (Finset.subset_univ s) (by omega), hs]
  simp

theorem tripleSupersets_card_edge_union {s t : Finset α} (hs : s.card = 2) (ht : t.card = 2) :
    (tripleSupersets (s ∪ t)).card =
      if s = t then Fintype.card α - 2 else if Disjoint s t then 0 else 1 := by
  classical
  by_cases he : s = t
  · subst t
    simp only [Finset.union_self, ite_true]
    exact tripleSupersets_card_two hs
  · rw [if_neg he]
    by_cases hd : Disjoint s t
    · rw [if_pos hd]
      apply tripleSupersets_card_four
      rw [Finset.card_union_eq_card_add_card.mpr hd, hs, ht]
    · rw [if_neg hd]
      exact tripleSupersets_card_three (two_subsets_union_card_three hs ht he hd)

theorem local_edges_eq_filter (t : Finset α) :
    t.powersetCard 2 = (Finset.univ.powersetCard 2).filter (· ⊆ t) := by
  ext s
  simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
  tauto

theorem triple_edge_weighted_incidence {E : Type*} [AddCommMonoid E] (w : Finset α → E) :
    (∑ t ∈ Finset.univ.powersetCard 3, ∑ s ∈ t.powersetCard 2, w s) =
      (Fintype.card α - 2) • ∑ s ∈ Finset.univ.powersetCard 2, w s := by
  classical
  conv_lhs =>
    arg 2
    ext t
    rw [local_edges_eq_filter t, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.sum_filter, Finset.sum_const]
  change (tripleSupersets s).card • w s = _
  rw [tripleSupersets_card_two (Finset.mem_powersetCard.mp hs).2]

end RepulsiveCoulomb
