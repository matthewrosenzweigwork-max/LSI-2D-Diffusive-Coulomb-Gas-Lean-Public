module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Elementary topology of an actual closed embedded ray attached to a closed
set at precisely its initial point. The nonempty-complement theorem is a direct
cut-point argument in the punctured plane; it assumes no ambient straightening.
These results do not assert that the complement is connected or simply connected. -/
noncomputable section
open Set Topology
open scoped NNReal
namespace RepulsiveCoulomb

/-- A closed embedded half-line cannot have compact range. -/
theorem closedEmbedding_nnreal_range_not_compact {X : Type*} [TopologicalSpace X]
    {γ : ℝ≥0 → X} (hγ : IsClosedEmbedding γ) : ¬ IsCompact (range γ) := by
  intro hc
  have hp : IsCompact (γ ⁻¹' range γ) := hγ.isCompact_preimage hc
  have hu : IsCompact (univ : Set ℝ≥0) := by simpa using hp
  exact not_bddAbove_univ hu.bddAbove

/-- Adjoining any set to a closed embedded half-line still gives a noncompact
set, provided the union itself were compact. -/
theorem union_closedEmbedding_nnreal_range_not_compact {X : Type*}
    [TopologicalSpace X] {K : Set X} {γ : ℝ≥0 → X}
    (hγ : IsClosedEmbedding γ) : ¬ IsCompact (K ∪ range γ) := by
  intro hc
  exact closedEmbedding_nnreal_range_not_compact hγ
    (hc.of_isClosed_subset hγ.isClosed_range subset_union_right)

/-- If deleting a point of a space leaves it connected, that space cannot be
covered by a closed set and a closed embedded ray meeting it only at the ray's
initial point. Cutting the ray at parameter one would separate the punctured
space into two closed pieces. -/
theorem closed_ray_attachment_compl_nonempty {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsClosed K) {γ : ℝ≥0 → X} (hγ : IsClosedEmbedding γ)
    (hmeet : range γ ∩ K = {γ 0})
    (hpunct : IsPreconnected ({γ 1}ᶜ : Set X)) :
    (K ∪ range γ)ᶜ.Nonempty := by
  by_contra hne
  have hcover : K ∪ range γ = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  let L : Set X := K ∪ γ '' Iic 1
  let R : Set X := γ '' Ici 1
  have hL : IsClosed L := hK.union (hγ.isClosedMap _ isClosed_Iic)
  have hR : IsClosed R := hγ.isClosedMap _ isClosed_Ici
  have hLR : ({γ 1}ᶜ : Set X) ⊆ L ∪ R := by
    intro x hx
    have hm : x ∈ K ∪ range γ := by rw [hcover]; trivial
    rcases hm with hKx | ⟨t, rfl⟩
    · exact Or.inl (Or.inl hKx)
    · rcases le_total t 1 with ht | ht
      · exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
      · exact Or.inr ⟨t, ht, rfl⟩
  have hleft : (({γ 1}ᶜ : Set X) ∩ L).Nonempty := by
    refine ⟨γ 0, ?_, Or.inr ⟨0, by norm_num, rfl⟩⟩
    change γ 0 ≠ γ 1
    exact fun he => (by norm_num : (0 : ℝ≥0) ≠ 1) (hγ.injective he)
  have hright : (({γ 1}ᶜ : Set X) ∩ R).Nonempty := by
    refine ⟨γ 2, ?_, ⟨2, by norm_num, rfl⟩⟩
    change γ 2 ≠ γ 1
    exact fun he => (by norm_num : (2 : ℝ≥0) ≠ 1) (hγ.injective he)
  obtain ⟨x, hx, hxL, t, ht, htx⟩ :=
    isPreconnected_closed_iff.mp hpunct L R hL hR hLR hleft hright
  have hx1 : x = γ 1 := by
    rcases hxL with hxK | ⟨s, hs, hsx⟩
    · have hx0 : x = γ 0 := by
        apply mem_singleton_iff.mp
        rw [← hmeet]
        exact ⟨⟨t, htx⟩, hxK⟩
      have ht0 : t = 0 := hγ.injective (htx.trans hx0)
      subst t
      norm_num at ht
    · have hst : s = t := hγ.injective (hsx.trans htx.symm)
      have ht1 : t = 1 := le_antisymm (hst ▸ hs) ht
      simpa [ht1] using htx.symm
  exact hx hx1

/-- In the actual complex plane the required punctured-space connectedness is
an existing dimension-two theorem. -/
theorem complex_closed_ray_attachment_compl_nonempty {K : Set ℂ}
    (hK : IsClosed K) {γ : ℝ≥0 → ℂ} (hγ : IsClosedEmbedding γ)
    (hmeet : range γ ∩ K = {γ 0}) : (K ∪ range γ)ᶜ.Nonempty :=
  closed_ray_attachment_compl_nonempty hK hγ hmeet
    (isConnected_compl_singleton_of_one_lt_rank
      (by simp [Complex.rank_real_complex]) (γ 1)).isPreconnected

end RepulsiveCoulomb
