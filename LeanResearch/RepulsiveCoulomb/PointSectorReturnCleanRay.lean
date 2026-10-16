module

public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments
public import LeanResearch.RepulsiveCoulomb.PlanarFirstReturnJordanCaps
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Isolated, uncompiled clean-old-ray facts for the full initial-angle bridge.
Compact escape follows from the actual metric ray, and carrier avoidance follows
from first contact plus the ordered opposite old-boundary halfline. -/
noncomputable section
open Set Topology
open scoped NNReal
namespace RepulsiveCoulomb

/-- A closed embedded nonnegative ray has positive points outside every
compact set. The point is constructed beyond the greatest compact preimage. -/
theorem nnreal_closedEmbedding_positive_escape
    {ρ : ℝ≥0 → ℂ} (hρ : IsClosedEmbedding ρ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ t : ℝ≥0, 0 < t ∧ ρ t ∉ K := by
  have hpre : IsCompact (ρ ⁻¹' insert (ρ 0) K) :=
    hρ.isCompact_preimage (hK.insert (ρ 0))
  obtain ⟨T, hT⟩ := hpre.exists_isGreatest ⟨0, by simp⟩
  refine ⟨T + 1, by positivity, ?_⟩
  intro hmem
  have hle : T + 1 ≤ T := hT.2 (Or.inr hmem)
  have hle' : (T : ℝ) + 1 ≤ (T : ℝ) := by exact_mod_cast hle
  linarith

/-- Compact escape of the SAME supplied positive metric ray, in the ordinary
complex-plane topology used by actual Jordan separation. -/
theorem pointMetricRay_positive_escape
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (ρ : ℝ → ℂ)
    (hd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t) :
    ∀ K : Set ℂ, IsCompact K → ∃ t : ℝ, 0 < t ∧ ρ t ∉ K := by
  let f : ℝ≥0 → ℂ := fun t => ρ t
  have hfmetric : ∀ s t : ℝ≥0,
      (pointSmoothConformalEDist a y (f s) (f t)).toReal = dist s t := by
    intro s t
    change (pointSmoothConformalEDist a y (ρ (s : ℝ)) (ρ (t : ℝ))).toReal =
      dist (s : ℝ) (t : ℝ)
    exact hd s s.prop t t.prop
  have hf := pointMetricRay_isClosedEmbedding ha y f hfmetric
  intro K hK
  obtain ⟨t, ht, hnot⟩ := nnreal_closedEmbedding_positive_escape hf hK
  exact ⟨(t : ℝ), by exact_mod_cast ht, hnot⟩

/-- The old clean end preceding the base parameter misses the actual cap
carrier. The new stopped ray meets the old boundary only at its endpoint times;
the compact old arc runs FORWARD from the base. This proves avoidance from
actual first contact and old-boundary order, rather than assuming cap exclusion. -/
theorem firstReturn_clean_old_end_avoids_carrier
    {P : Set ℂ} {b r ρ : ℝ → ℂ} (hbi : Function.Injective b)
    (hboundary : range b = frontier P)
    {z w s t : ℝ} (hzw : z < w) (hst : s < t)
    (hs : b s = r z) (ht : b t = r w)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P)
    (hρlower : ∀ v, 0 < v → ∃ u < s, b u = ρ v) :
    ∀ v, 0 < v → ρ v ∉ range (lineCapSegment r z w) ∪ range (lineCapSegment b s t) := by
  intro v hv hmem
  obtain ⟨u, hus, hu⟩ := hρlower v hv
  have hρfront : ρ v ∈ frontier P := by
    rw [← hboundary]
    exact ⟨u, hu⟩
  rcases hmem with hnew | hold
  · rw [lineCapSegment_range r hzw] at hnew
    obtain ⟨q, hq, he⟩ := hnew
    have hqends : q = z ∨ q = w := by
      by_contra hn
      have hqz : q ≠ z := fun h => hn (Or.inl h)
      have hqw : q ≠ w := fun h => hn (Or.inr h)
      have hqopen : q ∈ Ioo z w :=
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hqz), lt_of_le_of_ne hq.2 hqw⟩
      exact hgap q hqopen (he.symm ▸ hρfront)
    rcases hqends with rfl | rfl
    · have husEq : u = s := hbi (hu.trans (he.symm.trans hs.symm))
      exact hus.ne husEq
    · have hutEq : u = t := hbi (hu.trans (he.symm.trans ht.symm))
      exact (hus.trans hst).ne hutEq
  · rw [lineCapSegment_range b hst] at hold
    obtain ⟨q, hq, he⟩ := hold
    have huq : u = q := hbi (hu.trans he.symm)
    have hsu : s ≤ u := by simpa only [huq] using hq.1
    exact hus.not_ge hsu

end RepulsiveCoulomb
