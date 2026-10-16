module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Actual first and last hits of a continuous compact curve on a closed
separating boundary. The outer curve pieces stay in their prescribed closed
side. This is the finite topological extraction used to replace excursions by
an isometric boundary segment; no finite-crossing assertion is needed. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- A connected interval image missing a separating boundary stays on its
one anchored open side. -/
theorem continuous_interval_image_one_side {X : Type*} [TopologicalSpace X]
    {U V S : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Sᶜ) {γ : unitInterval → X} (hγ : Continuous γ)
    (s t : unitInterval)
    (havoid : ∀ u ∈ Icc s t, γ u ∉ S)
    (hanchor : ∃ u ∈ Icc s t, γ u ∈ U) : ∀ u ∈ Icc s t, γ u ∈ U := by
  have hsub : γ '' Icc s t ⊆ U ∪ V := by
    rintro z ⟨u, hu, rfl⟩
    exact hcover.symm ▸ havoid u hu
  have hmeet : (γ '' Icc s t ∩ U).Nonempty := by
    obtain ⟨u, hu, hUu⟩ := hanchor
    exact ⟨γ u, ⟨u, hu, rfl⟩, hUu⟩
  have hconn : IsPreconnected (γ '' Icc s t) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  have h := hconn.subset_left_of_subset_union hU hV hUV hsub hmeet
  intro u hu
  exact h ⟨u, hu, rfl⟩

/-- Either the curve already stays on the closed side, or its first/last
boundary hits enclose every possible excursion. Both outer pieces remain on
the closed side even if the curve has infinitely many boundary crossings. -/
theorem exists_first_last_boundary_hits_with_side_tails {X : Type*} [TopologicalSpace X]
    {U V S : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Sᶜ) (hfront : frontier U = S) (hS : IsClosed S)
    (γ : unitInterval → X) (hγ : Continuous γ)
    (hstart : γ 0 ∈ closure U) (hfinish : γ 1 ∈ closure U) :
    (∀ u, γ u ∈ closure U) ∨
      ∃ s t : unitInterval, s ≤ t ∧ γ s ∈ S ∧ γ t ∈ S ∧
        (∀ u, u ≤ s → γ u ∈ closure U) ∧
        (∀ u, t ≤ u → γ u ∈ closure U) := by
  have hcl : closure U = U ∪ S := by rw [closure_eq_self_union_frontier, hfront]
  have hScl : S ⊆ closure U := hfront ▸ frontier_subset_closure
  let K := γ ⁻¹' S
  have hK : IsCompact K := (hS.preimage hγ).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨s, hs⟩ := hK.exists_isLeast hne
    obtain ⟨t, ht⟩ := hK.exists_isGreatest hne
    refine Or.inr ⟨s, t, hs.2 ht.1, hs.1, ht.1, ?_, ?_⟩
    · intro u hus
      rcases eq_or_lt_of_le hus with he | hus'
      · exact he.symm ▸ hScl hs.1
      · have havoid : ∀ w ∈ Icc (0 : unitInterval) u, γ w ∉ S := by
          intro w hw hwS
          exact not_lt_of_ge ((hs.2 hwS).trans hw.2) hus'
        have hstartU : γ 0 ∈ U :=
          (hcl ▸ hstart).resolve_right (havoid 0 ⟨le_rfl, bot_le⟩)
        exact subset_closure (continuous_interval_image_one_side hU hV hUV hcover hγ
          0 u havoid ⟨0, ⟨le_rfl, bot_le⟩, hstartU⟩ u ⟨bot_le, le_rfl⟩)
    · intro u htu
      rcases eq_or_lt_of_le htu with he | htu'
      · exact he ▸ hScl ht.1
      · have havoid : ∀ w ∈ Icc u (1 : unitInterval), γ w ∉ S := by
          intro w hw hwS
          exact not_lt_of_ge (hw.1.trans (ht.2 hwS)) htu'
        have hfinishU : γ 1 ∈ U :=
          (hcl ▸ hfinish).resolve_right (havoid 1 ⟨le_top, le_rfl⟩)
        exact subset_closure (continuous_interval_image_one_side hU hV hUV hcover hγ
          u 1 havoid ⟨1, ⟨le_top, le_rfl⟩, hfinishU⟩ u ⟨le_rfl, le_top⟩)
  · have havoid : ∀ u : unitInterval, γ u ∉ S := fun u hu ↦ hne ⟨u, hu⟩
    have hstartU : γ 0 ∈ U := (hcl ▸ hstart).resolve_right (havoid 0)
    refine Or.inl (fun u ↦ subset_closure ?_)
    exact continuous_interval_image_one_side hU hV hUV hcover hγ 0 1
      (fun t _ ↦ havoid t) ⟨0, ⟨le_rfl, zero_le_one⟩, hstartU⟩ u ⟨bot_le, le_top⟩

end RepulsiveCoulomb
