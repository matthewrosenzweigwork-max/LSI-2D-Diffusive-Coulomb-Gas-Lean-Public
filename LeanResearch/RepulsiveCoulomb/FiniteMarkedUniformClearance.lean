module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Isometry

@[expose] public section

/-! A finite set separated from a closed set has one positive metric clearance.
In applications the closed set is the entire proper bottom ray, not a bounded
prefix. This elementary result is independent of any chart continuation. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The lower bound is uniform over the whole closed set, even if unbounded.
Empty finite marked sets are allowed. -/
theorem finite_closed_uniform_clearance {X : Type*} [MetricSpace X]
    {S C : Set X} (hS : S.Finite) (hC : IsClosed C) (hdisj : Disjoint S C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, ∀ x ∈ C, δ < dist z x := by
  obtain ⟨r, hr, hdist⟩ := Metric.exists_pos_forall_lt_edist hS.isCompact hC hdisj
  refine ⟨(r : ℝ), hr, ?_⟩
  intro z hz x hx
  have h := hdist z hz x hx
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h

/-- A single choice may simultaneously respect the initial corner-chart
radius and the first marked adjacent-edge parameter. Neither bound depends on R. -/
theorem finite_closed_uniform_clearance_below {X : Type*} [MetricSpace X]
    {S C : Set X} (hS : S.Finite) (hC : IsClosed C) (hdisj : Disjoint S C)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < L ∧ δ < ε ∧
      ∀ z ∈ S, ∀ x ∈ C, δ < dist z x := by
  obtain ⟨d, hd, hdist⟩ := finite_closed_uniform_clearance hS hC hdisj
  let δ := min d (min L ε) / 2
  have hm : 0 < min d (min L ε) := lt_min hd (lt_min hL hε)
  have hδ : 0 < δ := half_pos hm
  have hδm : δ < min d (min L ε) := half_lt_self hm
  refine ⟨δ, hδ, hδm.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
    hδm.trans_le ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro z hz x hx
  exact (hδm.trans_le (min_le_left _ _)).trans (hdist z hz x hx)

/-- This is the exact no-mark argument at a completed finite rectangle. It
uses distance to one corresponding bottom point, not nearest-point existence. -/
theorem not_mem_marked_of_distance_to_closed_le {X : Type*} [MetricSpace X]
    {S C : Set X} {δ : ℝ}
    (hclear : ∀ z ∈ S, ∀ x ∈ C, δ < dist z x)
    {p x : X} (hx : x ∈ C) (hp : dist p x ≤ δ) : p ∉ S := by
  intro hpS
  exact (hclear p hpS x hx).not_ge hp

/-- An isometric copy of any complete source has closed range. In particular
NNReal supplies a whole closed proper ray and Real supplies a whole line. -/
theorem finite_isometric_range_uniform_clearance {X Y : Type*}
    [MetricSpace X] [CompleteSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Isometry f) {S : Set Y}
    (hS : S.Finite) (hdisj : Disjoint S (range f)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, ∀ x, δ < dist z (f x) := by
  obtain ⟨δ, hδ, hd⟩ :=
    finite_closed_uniform_clearance hS hf.isClosedEmbedding.isClosed_range hdisj
  exact ⟨δ, hδ, fun z hz x ↦ hd z hz (f x) (mem_range_self x)⟩

end RepulsiveCoulomb
