module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic

@[expose] public section

/-!
# Arclength parametrization of a proper topological boundary clock

This file is an isolated source-only candidate. It has not been compiled.

A closed embedded real clock in a proper metric space becomes a full metric
line if every pair of clock points is joined by a minimizing segment contained
in its range. No unit-speed hypothesis on the original clock is used.

The two mechanisms are separate:
* contained minimizing segments and the topological inverse give distance
  additivity in the original real order;
* properness rules out finite length at either end of that order.
-/

noncomputable section

open Set Topology

namespace ProperBoundaryClock

variable {X : Type*} [MetricSpace X]

/-- Every two points on the clock admit a constant-speed minimizing segment
whose entire image stays on the clock. -/
def HasContainedMinimizingSegments (β : ℝ → X) : Prop :=
  ∀ s t : ℝ, ∃ γ : unitInterval → X,
    Continuous γ ∧
    γ 0 = β s ∧
    γ 1 = β t ∧
    Set.range γ ⊆ Set.range β ∧
    ∀ u v : unitInterval,
      dist (γ u) (γ v) = |(u : ℝ) - (v : ℝ)| * dist (β s) (β t)

/-- Distance is additive along the order supplied by any embedded clock whose
range contains a minimizing segment between every pair of its points. -/
theorem dist_additive_of_contained_segments
    {β : ℝ → X} (hβ : IsEmbedding β)
    (hgeo : HasContainedMinimizingSegments β)
    {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u) := by
  obtain ⟨γ, hγcont, hγzero, hγone, hγrange, hγdist⟩ := hgeo s u
  let e : ℝ ≃ₜ Set.range β := hβ.toHomeomorph
  let γr : unitInterval → Set.range β :=
    fun v => ⟨γ v, hγrange ⟨v, rfl⟩⟩
  let δ : unitInterval → ℝ := fun v => e.symm (γr v)
  have hγrcont : Continuous γr :=
    hγcont.subtype_mk (fun v => hγrange ⟨v, rfl⟩)
  have hδcont : Continuous δ := e.symm.continuous.comp hγrcont
  have hβδ (v : unitInterval) : β (δ v) = γ v := by
    change ((e (e.symm (γr v))) : X) = γ v
    exact congrArg Subtype.val (e.apply_symm_apply (γr v))
  have hδzero : δ 0 = s := hβ.injective (by rw [hβδ, hγzero])
  have hδone : δ 1 = u := hβ.injective (by rw [hβδ, hγone])
  have ht : t ∈ Set.Icc (δ 0) (δ 1) := by
    rw [hδzero, hδone]
    exact ⟨hst, htu⟩
  obtain ⟨v, hv⟩ := intermediate_value_univ
    (0 : unitInterval) (1 : unitInterval) hδcont ht
  have hvγ : γ v = β t := by rw [← hβδ v, hv]
  have hleft := hγdist (0 : unitInterval) v
  have hright := hγdist v (1 : unitInterval)
  simp [hγzero, hvγ, abs_of_nonneg v.property.1] at hleft
  simp [hvγ, hγone, abs_of_nonpos (sub_nonpos.mpr v.property.2)] at hright
  nlinarith

/-- Signed distance from the point at original time zero. The sign records the
original topological orientation; it does not assume an arclength clock. -/
def signedDistance (β : ℝ → X) (t : ℝ) : ℝ :=
  if 0 ≤ t then dist (β 0) (β t) else -dist (β 0) (β t)

@[simp] theorem signedDistance_zero (β : ℝ → X) : signedDistance β 0 = 0 := by
  simp [signedDistance]

/-- Additivity identifies every ordered clock increment with ambient distance. -/
theorem signedDistance_sub_of_le
    {β : ℝ → X}
    (hadd : ∀ s t u : ℝ, s ≤ t → t ≤ u →
      dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u))
    {s t : ℝ} (hst : s ≤ t) :
    signedDistance β t - signedDistance β s = dist (β s) (β t) := by
  by_cases hs : 0 ≤ s
  · have ht : 0 ≤ t := hs.trans hst
    have h := hadd 0 s t hs hst
    simp only [signedDistance, if_pos hs, if_pos ht]
    linarith
  · by_cases ht : 0 ≤ t
    · have hs0 : s ≤ 0 := (lt_of_not_ge hs).le
      have h := hadd s 0 t hs0 ht
      rw [dist_comm (β s) (β 0)] at h
      simp only [signedDistance, if_neg hs, if_pos ht]
      linarith
    · have ht0 : t ≤ 0 := (lt_of_not_ge ht).le
      have h := hadd s t 0 hst ht0
      rw [dist_comm (β s) (β 0), dist_comm (β t) (β 0)] at h
      simp only [signedDistance, if_neg hs, if_neg ht]
      linarith

/-- Signed distance preserves the ambient metric of all clock points. -/
theorem signedDistance_dist
    {β : ℝ → X}
    (hadd : ∀ s t u : ℝ, s ≤ t → t ≤ u →
      dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u))
    (s t : ℝ) :
    dist (signedDistance β s) (signedDistance β t) = dist (β s) (β t) := by
  rcases le_total s t with hst | hts
  · rw [Real.dist_eq, abs_sub_comm,
      signedDistance_sub_of_le hadd hst, abs_of_nonneg dist_nonneg]
  · rw [Real.dist_eq, signedDistance_sub_of_le hadd hts,
      abs_of_nonneg dist_nonneg, dist_comm]

/-- A positive tail of a proper embedded clock cannot stay in a bounded ball. -/
theorem exists_positive_far_point [ProperSpace X]
    {β : ℝ → X} (hβ : IsClosedEmbedding β) (R : ℝ) :
    ∃ t : ℝ, 0 < t ∧ R < dist (β 0) (β t) := by
  have hc : IsCompact (β ⁻¹' Metric.closedBall (β 0) R) :=
    hβ.isProperMap.isCompact_preimage (isCompact_closedBall (β 0) R)
  obtain ⟨M, hM⟩ := hc.bddAbove
  let t : ℝ := max M 0 + 1
  have hMt : M < t := by dsimp [t]; linarith [le_max_left M (0 : ℝ)]
  have h0t : 0 < t := by dsimp [t]; linarith [le_max_right M (0 : ℝ)]
  refine ⟨t, h0t, ?_⟩
  by_contra h
  have ht : t ∈ β ⁻¹' Metric.closedBall (β 0) R := by
    exact Metric.mem_closedBall'.2 (le_of_not_gt h)
  exact (not_le_of_gt hMt) (hM ht)

/-- A negative tail of a proper embedded clock cannot stay in a bounded ball. -/
theorem exists_negative_far_point [ProperSpace X]
    {β : ℝ → X} (hβ : IsClosedEmbedding β) (R : ℝ) :
    ∃ t : ℝ, t < 0 ∧ R < dist (β 0) (β t) := by
  have hc : IsCompact (β ⁻¹' Metric.closedBall (β 0) R) :=
    hβ.isProperMap.isCompact_preimage (isCompact_closedBall (β 0) R)
  obtain ⟨M, hM⟩ := hc.bddBelow
  let t : ℝ := min M 0 - 1
  have htM : t < M := by dsimp [t]; linarith [min_le_left M (0 : ℝ)]
  have ht0 : t < 0 := by dsimp [t]; linarith [min_le_right M (0 : ℝ)]
  refine ⟨t, ht0, ?_⟩
  by_contra h
  have ht : t ∈ β ⁻¹' Metric.closedBall (β 0) R := by
    exact Metric.mem_closedBall'.2 (le_of_not_gt h)
  exact (not_le_of_gt htM) (hM ht)

/-- Properness makes signed distance onto, even before distance additivity is
used. Continuity and the topological two-ended clock supply both signs. -/
theorem signedDistance_surjective [ProperSpace X]
    {β : ℝ → X} (hβ : IsClosedEmbedding β) :
    Function.Surjective (signedDistance β) := by
  have hdcont : Continuous (fun t : ℝ => dist (β 0) (β t)) :=
    continuous_const.dist hβ.continuous
  intro a
  by_cases ha : 0 ≤ a
  · obtain ⟨t, ht0, htfar⟩ := exists_positive_far_point hβ a
    have haI : a ∈ Set.Icc (dist (β 0) (β 0)) (dist (β 0) (β t)) := by
      simpa only [dist_self, Set.mem_Icc] using And.intro ha htfar.le
    obtain ⟨s, hs, hsa⟩ := intermediate_value_Icc ht0.le hdcont.continuousOn haI
    exact ⟨s, by simpa only [signedDistance, if_pos hs.1] using hsa⟩
  · have halt : a < 0 := lt_of_not_ge ha
    obtain ⟨t, ht0, htfar⟩ := exists_negative_far_point hβ (-a)
    have haI : -a ∈ Set.Icc (dist (β 0) (β 0)) (dist (β 0) (β t)) := by
      simp only [dist_self, Set.mem_Icc]
      exact ⟨by linarith, htfar.le⟩
    obtain ⟨s, hs, hsa⟩ := intermediate_value_Icc' ht0.le hdcont.continuousOn haI
    have hsneg : ¬ 0 ≤ s := by
      intro hs0
      have hs_eq : s = 0 := le_antisymm hs.2 hs0
      have hz : (0 : ℝ) = -a := by simpa only [hs_eq, dist_self] using hsa
      linarith
    refine ⟨s, ?_⟩
    simp only [signedDistance, if_neg hsneg]
    linarith

/-- The source-only metric conclusion. In addition to the full-line isometry
and exact range equality, the final identity specifies the signed-distance
reparametrization of the original boundary clock. -/
theorem exists_isometry_range_eq_of_contained_segments [ProperSpace X]
    {β : ℝ → X} (hβ : IsClosedEmbedding β)
    (hgeo : HasContainedMinimizingSegments β) :
    ∃ ℓ : ℝ → X, Isometry ℓ ∧ Set.range ℓ = Set.range β ∧
      ∀ t : ℝ, ℓ (signedDistance β t) = β t := by
  have hadd : ∀ s t u : ℝ, s ≤ t → t ≤ u →
      dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u) :=
    fun _ _ _ hst htu =>
      dist_additive_of_contained_segments hβ.isEmbedding hgeo hst htu
  have hdist := signedDistance_dist hadd
  have hsurj := signedDistance_surjective hβ
  let c : ℝ → ℝ := fun a => Classical.choose (hsurj a)
  have hc (a : ℝ) : signedDistance β (c a) = a := Classical.choose_spec (hsurj a)
  let ℓ : ℝ → X := fun a => β (c a)
  have hℓ : Isometry ℓ := by
    apply Isometry.of_dist_eq
    intro a b
    change dist (β (c a)) (β (c b)) = dist a b
    rw [← hdist (c a) (c b), hc a, hc b]
  have hparam (t : ℝ) : ℓ (signedDistance β t) = β t := by
    apply dist_eq_zero.mp
    change dist (β (c (signedDistance β t))) (β t) = 0
    rw [← hdist, hc, dist_self]
  refine ⟨ℓ, hℓ, ?_, hparam⟩
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    exact ⟨c a, rfl⟩
  · rintro x ⟨t, rfl⟩
    exact ⟨signedDistance β t, hparam t⟩

/-- Closed-subset version, suitable when the topological boundary clock is
presented as a homeomorphism onto the boundary subtype. -/
theorem exists_isometry_range_eq_of_homeomorph [ProperSpace X]
    {B : Set X} (hB : IsClosed B) (e : ℝ ≃ₜ B)
    (hgeo : HasContainedMinimizingSegments (fun t => (e t : X))) :
    ∃ ℓ : ℝ → X, Isometry ℓ ∧ Set.range ℓ = B ∧
      ∀ t : ℝ, ℓ (signedDistance (fun u => (e u : X)) t) = (e t : X) := by
  let β : ℝ → X := fun t => (e t : X)
  have hβ : IsClosedEmbedding β :=
    hB.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
  obtain ⟨ℓ, hℓ, hrange, hparam⟩ :=
    exists_isometry_range_eq_of_contained_segments hβ hgeo
  refine ⟨ℓ, hℓ, hrange.trans ?_, hparam⟩
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (e t).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    change ((e (e.symm ⟨x, hx⟩)) : X) = x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

end ProperBoundaryClock
