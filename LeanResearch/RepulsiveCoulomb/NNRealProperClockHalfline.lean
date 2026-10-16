import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Maps.Proper.Basic

/-!
SOURCE-ONLY, UNCOMPILED. A proper injective continuous nonnegative clock
has exactly one closed halfline as its complete range. Its orientation is
derived from continuity and injectivity; compact escape and IVT exclude a
finite missing endpoint. No halfline range is assumed.
-/

noncomputable section
open Set Topology
open scoped NNReal

namespace RepulsiveCoulomb

/-- Compact-preimage properness gives actual positive compact escape. This
version is independent of any metric or planar model. -/
theorem nnreal_compactPreimage_positive_escape
    {X : Type*} [TopologicalSpace X] {f : ℝ≥0 → X}
    (hproper : ∀ K : Set X, IsCompact K → IsCompact (f ⁻¹' K))
    {K : Set X} (hK : IsCompact K) :
    ∃ u : ℝ≥0, 0 < u ∧ f u ∉ K := by
  have hpre : IsCompact (f ⁻¹' insert (f 0) K) :=
    hproper _ (hK.insert (f 0))
  obtain ⟨T, hT⟩ := hpre.exists_isGreatest ⟨0, by simp⟩
  refine ⟨T + 1, add_pos_of_nonneg_of_pos (zero_le : (0 : ℝ≥0) ≤ T) zero_lt_one, ?_⟩
  intro hmem
  have hle : T + 1 ≤ T := hT.2 (Or.inr hmem)
  exact (not_le.mpr (lt_add_of_pos_right T zero_lt_one)) hle

/-- IVT fills every point above the initial value of an increasing clock;
compact escape supplies the upper IVT endpoint. -/
theorem nnreal_strictMono_range_of_compact_escape
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (hmono : StrictMono f)
    (hescape : ∀ K : Set ℝ, IsCompact K → ∃ u : ℝ≥0, f u ∉ K) :
    range f = Ici (f 0) := by
  apply Subset.antisymm
  · rintro x ⟨u, rfl⟩
    exact hmono.monotone (zero_le : (0 : ℝ≥0) ≤ u)
  · intro x hx
    obtain ⟨u, hu⟩ := hescape (Icc (f 0) x) isCompact_Icc
    have hxu : x < f u := by
      by_contra hn
      exact hu ⟨hmono.monotone (zero_le : (0 : ℝ≥0) ≤ u), le_of_not_gt hn⟩
    obtain ⟨v, _, hv⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ u)
      hf.continuousOn ⟨hx, hxu.le⟩
    exact ⟨v, hv⟩

/-- The decreasing orientation is treated with the reversed IVT. -/
theorem nnreal_strictAnti_range_of_compact_escape
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (hanti : StrictAnti f)
    (hescape : ∀ K : Set ℝ, IsCompact K → ∃ u : ℝ≥0, f u ∉ K) :
    range f = Iic (f 0) := by
  apply Subset.antisymm
  · rintro x ⟨u, rfl⟩
    exact hanti.antitone (zero_le : (0 : ℝ≥0) ≤ u)
  · intro x hx
    obtain ⟨u, hu⟩ := hescape (Icc x (f 0)) isCompact_Icc
    have hux : f u < x := by
      by_contra hn
      exact hu ⟨le_of_not_gt hn, hanti.antitone (zero_le : (0 : ℝ≥0) ≤ u)⟩
    obtain ⟨v, _, hv⟩ := intermediate_value_Icc' (zero_le : (0 : ℝ≥0) ≤ u)
      hf.continuousOn ⟨hux.le, hx⟩
    exact ⟨v, hv⟩

/-- The orientation is a conclusion, not a chosen boundary normalization. -/
theorem nnreal_injective_continuous_range_halfline_of_compact_escape
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (hfi : Function.Injective f)
    (hescape : ∀ K : Set ℝ, IsCompact K → ∃ u : ℝ≥0, f u ∉ K) :
    (StrictMono f ∧ range f = Ici (f 0)) ∨
      (StrictAnti f ∧ range f = Iic (f 0)) := by
  rcases hf.strictMono_of_inj hfi with hmono | hanti
  · exact Or.inl ⟨hmono, nnreal_strictMono_range_of_compact_escape hf hmono hescape⟩
  · exact Or.inr ⟨hanti, nnreal_strictAnti_range_of_compact_escape hf hanti hescape⟩

/-- Standard properness form of the clock classification. -/
theorem nnreal_proper_clock_range_halfline
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (hfi : Function.Injective f)
    (hproper : ∀ K : Set ℝ, IsCompact K → IsCompact (f ⁻¹' K)) :
    (StrictMono f ∧ range f = Ici (f 0)) ∨
      (StrictAnti f ∧ range f = Iic (f 0)) := by
  apply nnreal_injective_continuous_range_halfline_of_compact_escape hf hfi
  intro K hK
  obtain ⟨u, _, hu⟩ := nnreal_compactPreimage_positive_escape hproper hK
  exact ⟨u, hu⟩

theorem nnreal_isProperMap_range_halfline
    {f : ℝ≥0 → ℝ} (hf : IsProperMap f) (hfi : Function.Injective f) :
    (StrictMono f ∧ range f = Ici (f 0)) ∨
      (StrictAnti f ∧ range f = Iic (f 0)) := by
  exact nnreal_proper_clock_range_halfline hf.continuous hfi
    (fun _ hK => hf.isCompact_preimage hK)

/-- Closed embeddings furnish the precise properness used above. -/
theorem nnreal_closedEmbedding_range_halfline
    {f : ℝ≥0 → ℝ} (hf : IsClosedEmbedding f) :
    (StrictMono f ∧ range f = Ici (f 0)) ∨
      (StrictAnti f ∧ range f = Iic (f 0)) := by
  exact nnreal_proper_clock_range_halfline hf.continuous hf.injective
    (fun _ hK => hf.isCompact_preimage hK)

end RepulsiveCoulomb
