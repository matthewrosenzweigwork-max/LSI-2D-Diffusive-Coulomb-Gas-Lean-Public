module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicSubedge
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Actual first/last-intersection extraction for a shortcut joining two arcs.
The extracted middle interval meets each of the two closed sets at precisely
one endpoint. No finite-intersection assumption is used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_curve_bridge_interval {X : Type*} [TopologicalSpace X]
    (γ : Icc (0 : ℝ) 1 → X) (hc : Continuous γ) {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B)
    (h0 : γ ⟨0, by norm_num⟩ ∈ A) (h1 : γ ⟨1, by norm_num⟩ ∈ B)
    (hdisj : Disjoint (γ ⁻¹' A) (γ ⁻¹' B)) :
    ∃ s t : Icc (0 : ℝ) 1, s < t ∧ γ s ∈ A ∧ γ t ∈ B ∧
      (γ '' Icc s t) ∩ A = {γ s} ∧ (γ '' Icc s t) ∩ B = {γ t} := by
  have hCA : IsClosed (γ ⁻¹' A) := hA.preimage hc
  obtain ⟨s, hs⟩ := hCA.isCompact.exists_isGreatest ⟨⟨0, by norm_num⟩, h0⟩
  have hCB : IsClosed ((γ ⁻¹' B) ∩ Ici s) := (hB.preimage hc).inter isClosed_Ici
  have hCBne : ((γ ⁻¹' B) ∩ Ici s).Nonempty := ⟨⟨1, by norm_num⟩, h1, s.2.2⟩
  obtain ⟨t, ht⟩ := hCB.isCompact.exists_isLeast hCBne
  have hst : s < t := by
    apply lt_of_le_of_ne (a := s) (b := t) ht.1.2
    intro he
    exact hdisj.le_bot ⟨hs.1, he.symm ▸ ht.1.1⟩
  refine ⟨s, t, hst, hs.1, ht.1.1, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨u, hu, rfl⟩, hzA⟩
      have hus : u = s := le_antisymm (hs.2 hzA) hu.1
      simpa only [hus] using mem_singleton (γ s)
    · rintro z hz
      obtain rfl := mem_singleton_iff.mp hz
      exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, hs.1⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨u, hu, rfl⟩, hzB⟩
      have hut : u = t := le_antisymm hu.2 (ht.2 ⟨hzB, hu.1⟩)
      simpa only [hut] using mem_singleton (γ t)
    · rintro z hz
      obtain rfl := mem_singleton_iff.mp hz
      exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, ht.1.1⟩

/-- A strictly shorter exact geodesic joining the outer endpoints of two legs
cannot pass through their common center. -/
theorem pointGeodesic_shortcut_avoids_center {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : PointGeodesicTreeEdge a y) (q : ℂ)
    (hshort : (pointSmoothConformalEDist a y γ.start γ.finish).toReal <
      (pointSmoothConformalEDist a y γ.start q).toReal +
        (pointSmoothConformalEDist a y q γ.finish).toReal) : q ∉ range γ.curve := by
  rintro ⟨t, ht⟩
  have hleft := γ.geodesic ⟨0, by norm_num⟩ t
  have hright := γ.geodesic t ⟨1, by norm_num⟩
  rw [γ.curve_start, ht, sub_zero, abs_of_nonneg t.2.1] at hleft
  rw [γ.curve_finish, ht, abs_of_nonneg (sub_nonneg.mpr t.2.2)] at hright
  rw [hleft, hright] at hshort
  nlinarith

/-- With two genuinely disjoint legs, a strictly shorter actual minimizing
shortcut contains a simple subedge touching each leg only at one endpoint. -/
theorem exists_pointGeodesic_shortcut_bridge {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (A B γ : PointGeodesicTreeEdge a y) (q : ℂ)
    (hA : A.start = q) (hB : B.start = q)
    (hγA : γ.start = A.finish) (hγB : γ.finish = B.finish)
    (hmeet : range A.curve ∩ range B.curve = {q})
    (hshort : (pointSmoothConformalEDist a y γ.start γ.finish).toReal <
      (pointSmoothConformalEDist a y γ.start q).toReal +
        (pointSmoothConformalEDist a y q γ.finish).toReal) :
    ∃ s t : Icc (0 : ℝ) 1, s < t ∧
      γ.curve s ∈ range A.curve ∧ γ.curve t ∈ range B.curve ∧
      (γ.curve '' Icc s t) ∩ range A.curve = {γ.curve s} ∧
      (γ.curve '' Icc s t) ∩ range B.curve = {γ.curve t} ∧
      γ.curve s ≠ q ∧ γ.curve t ≠ q := by
  have havoid := pointGeodesic_shortcut_avoids_center ha y γ q hshort
  have hdisj : Disjoint (γ.curve ⁻¹' range A.curve) (γ.curve ⁻¹' range B.curve) := by
    apply disjoint_left.mpr
    intro t htA htB
    have hq : γ.curve t = q := mem_singleton_iff.mp (hmeet ▸ And.intro htA htB)
    exact havoid ⟨t, hq⟩
  obtain ⟨s, t, hst, hs, ht, hmeetA, hmeetB⟩ :=
    exists_curve_bridge_interval γ.curve γ.continuous
      (isCompact_range A.continuous).isClosed (isCompact_range B.continuous).isClosed
      (by rw [γ.curve_start, hγA]; exact ⟨⟨1, by norm_num⟩, A.curve_finish⟩)
      (by rw [γ.curve_finish, hγB]; exact ⟨⟨1, by norm_num⟩, B.curve_finish⟩) hdisj
  exact ⟨s, t, hst, hs, ht, hmeetA, hmeetB,
    fun h ↦ havoid ⟨s, h⟩, fun h ↦ havoid ⟨t, h⟩⟩

end RepulsiveCoulomb
