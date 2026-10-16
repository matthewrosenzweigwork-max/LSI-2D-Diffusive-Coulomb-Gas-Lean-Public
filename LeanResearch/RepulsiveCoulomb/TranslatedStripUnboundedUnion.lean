import LeanResearch.RepulsiveCoulomb.TranslatedStripWidthSupremum
import Mathlib.Topology.Connected.Clopen

/-!
SOURCE-ONLY, UNCOMPILED. The union of an unbounded family of literal translated
strips is the closed Euclidean wedge. Compatible genuine isometries glue there.
Every source point lies strictly below the top of a larger actual stage; hence
the glued image is the union of the below-top stage images. These statements
supply the infinite-width obstruction without an exhaustion hypothesis.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- The literal complex wedge, with the inherited Euclidean metric. -/
def flatTranslatedWedge (v : ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 ≤ r ∧ ∃ u : ℝ, 0 ≤ u ∧ z = flatShearedPoint v r u}

theorem flatTranslatedWedge_image {v : ℂ} (hvi : v.im ≠ 0) :
    flatTranslatedWedge v =
      (flatShearHomeomorph hvi) '' (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) := by
  ext z
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    exact ⟨(r, u), ⟨hr, hu⟩, rfl⟩
  · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
    exact ⟨r, hr, u, hu, rfl⟩

theorem flatTranslatedWedge_isClosed {v : ℂ} (hvi : v.im ≠ 0) :
    IsClosed (flatTranslatedWedge v) := by
  rw [flatTranslatedWedge_image hvi]
  exact (flatShearHomeomorph hvi).isClosedMap _ (isClosed_Ici.prod isClosed_Ici)

theorem flatShearedStrip_subset_wedge {v : ℂ} {s : ℝ} :
    flatShearedStrip v s ⊆ flatTranslatedWedge v := by
  rintro z ⟨r, hr, u, hu, hz⟩
  exact ⟨r, hr, u, hu.1, hz⟩

/-- Unbounded widths cover the whole wedge, not just a dense subset. -/
theorem iUnion_shearedStrips_eq_wedge {v : ℂ} {W : Set ℝ}
    (hW : ¬ BddAbove W) :
    (⋃ s : W, flatShearedStrip v s.1) = flatTranslatedWedge v := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨s, hs⟩ := mem_iUnion.mp hz
    exact flatShearedStrip_subset_wedge hs
  · rintro z ⟨r, hr, u, hu, hz⟩
    obtain ⟨s, hs, hus⟩ := not_bddAbove_iff.mp hW u
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, r, hr, u, ⟨hu, hus.le⟩, hz⟩

theorem shearedStrips_directed {v : ℂ} (W : Set ℝ) :
    Directed (· ⊆ ·) (fun s : W ↦ flatShearedStrip v s.1) := by
  intro s t
  rcases le_total s.1 t.1 with hst | hts
  · exact ⟨t, flatShearedStrip_mono hst, subset_rfl⟩
  · exact ⟨s, subset_rfl, flatShearedStrip_mono hts⟩

/-- The infinite union has closed image because its actual source is complete.
No target completeness, limiting map, properness or image-closedness premise
is needed. -/
theorem shearedStripUnion_isClosed_range
    {Y : Type*} [MetricSpace Y] {v : ℂ} (hvi : v.im ≠ 0)
    {W : Set ℝ} (hW : ¬ BddAbove W)
    (f : ∀ s : W, flatShearedStrip v s.1 → Y)
    (hf : ∀ s, Isometry (f s))
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedStrip v s.1)
      (ht : z ∈ flatShearedStrip v t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩) :
    IsClosed (range (directedFlatUnion (fun s : W ↦ flatShearedStrip v s.1) f hcompat)) := by
  let U : W → Set ℂ := fun s ↦ flatShearedStrip v s.1
  have hUc : IsClosed (⋃ s, U s) := by
    rw [show (⋃ s, U s) = flatTranslatedWedge v from iUnion_shearedStrips_eq_wedge hW]
    exact flatTranslatedWedge_isClosed hvi
  letI : CompleteSpace (⋃ s, U s) := hUc.isComplete.completeSpace_coe
  exact (directedFlatUnion_isometry U f (shearedStrips_directed W) hcompat hf).isClosedEmbedding.isClosed_range

/-- Every image point is below the top of some larger genuine stage. This is
why relative openness at all finite stages implies openness of the whole wedge
image, including its apex and both unbounded boundary rays. -/
theorem shearedStripUnion_range_eq_iUnion_without_top
    {Y : Type*} [MetricSpace Y] {v : ℂ} (hvi : v.im ≠ 0)
    {W : Set ℝ} (hW : ¬ BddAbove W) (hWpos : ∀ s ∈ W, 0 < s)
    (f : ∀ s : W, flatShearedStrip v s.1 → Y)
    (hf : ∀ s, Isometry (f s))
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedStrip v s.1)
      (ht : z ∈ flatShearedStrip v t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩) :
    range (directedFlatUnion (fun s : W ↦ flatShearedStrip v s.1) f hcompat) =
      ⋃ s : W, range (f s) \ range (f s ∘ translatedStripTop (hWpos s.1 s.2).le) := by
  let U : W → Set ℂ := fun s ↦ flatShearedStrip v s.1
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := mem_iUnion.mp x.2
    obtain ⟨r, hr, u, hu, hxu⟩ := hs
    obtain ⟨t, ht, hut⟩ := not_bddAbove_iff.mp hW u
    let j : W := ⟨t, ht⟩
    have hxj : x.1 ∈ U j := ⟨r, hr, u, ⟨hu.1, hut.le⟩, hxu⟩
    rw [directedFlatUnion_of_mem U f hcompat x j hxj]
    apply mem_iUnion.mpr
    refine ⟨j, ⟨⟨x.1, hxj⟩, rfl⟩, ?_⟩
    rw [translatedStrip_image_mem_top_iff hvi (hWpos j.1 j.2).le
      (hf j).injective ⟨x.1, hxj⟩ hr hxu]
    exact ne_of_lt hut
  · intro hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    obtain ⟨x, rfl⟩ := hs.1
    exact ⟨⟨x.1, mem_iUnion.mpr ⟨s, x.2⟩⟩,
      directedFlatUnion_apply U f hcompat s x⟩

/-- An explicit entire-wedge isometry constructed from the compatible strips.
This can also be used independently of the point-metric exhaustion argument. -/
theorem exists_shearedWedge_isometry_of_unbounded_widths
    {Y : Type*} [MetricSpace Y] {v : ℂ} {W : Set ℝ}
    (hW : ¬ BddAbove W)
    (f : ∀ s : W, flatShearedStrip v s.1 → Y)
    (hf : ∀ s, Isometry (f s))
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedStrip v s.1)
      (ht : z ∈ flatShearedStrip v t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩) :
    ∃ F : flatTranslatedWedge v → Y, Isometry F ∧
      ∀ s (z : flatShearedStrip v s.1),
        F ⟨z.1, flatShearedStrip_subset_wedge z.2⟩ = f s z := by
  let U : W → Set ℂ := fun s ↦ flatShearedStrip v s.1
  have hU : (⋃ s, U s) = flatTranslatedWedge v := iUnion_shearedStrips_eq_wedge hW
  let incl : flatTranslatedWedge v → ⋃ s, U s := fun z ↦ ⟨z.1, hU.symm ▸ z.2⟩
  have hi : Isometry incl := fun _ _ ↦ rfl
  refine ⟨directedFlatUnion U f hcompat ∘ incl,
    (directedFlatUnion_isometry U f (shearedStrips_directed W) hcompat hf).comp hi, ?_⟩
  intro s z
  exact directedFlatUnion_apply U f hcompat s z

end RepulsiveCoulomb
