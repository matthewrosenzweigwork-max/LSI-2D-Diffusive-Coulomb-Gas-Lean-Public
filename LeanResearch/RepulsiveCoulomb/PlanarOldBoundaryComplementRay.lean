import LeanResearch.RepulsiveCoulomb.NNRealProperClockHalfline
import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfplaneHomeomorphisms
import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
SOURCE-ONLY, UNCOMPILED. Construct the untouched proper old-boundary ray
from the actual old halfplane straightening and an actual closed embedded
removed-boundary ray. This is a carrier lemma, not a residual-side theorem.

The input removed ray may traverse a compact old edge and then an old ray.
Its metric speed, affine clock, and preferred orientation are irrelevant.
-/

noncomputable section
open Set Topology
open scoped NNReal

namespace RepulsiveCoulomb

def oldBoundaryRayPlus (b : ℝ → ℂ) (c : ℝ) (u : ℝ≥0) : ℂ :=
  b (c + (u : ℝ))

def oldBoundaryRayMinus (b : ℝ → ℂ) (c : ℝ) (u : ℝ≥0) : ℂ :=
  b (c - (u : ℝ))

@[simp] theorem oldBoundaryRayPlus_zero (b : ℝ → ℂ) (c : ℝ) :
    oldBoundaryRayPlus b c 0 = b c := by simp [oldBoundaryRayPlus]

@[simp] theorem oldBoundaryRayMinus_zero (b : ℝ → ℂ) (c : ℝ) :
    oldBoundaryRayMinus b c 0 = b c := by simp [oldBoundaryRayMinus]

theorem oldBoundaryRayPlus_isClosedEmbedding
    {b : ℝ → ℂ} (hb : IsClosedEmbedding b) (c : ℝ) :
    IsClosedEmbedding (oldBoundaryRayPlus b c) := by
  exact hb.comp ((Homeomorph.addLeft c).isClosedEmbedding.comp
    NNReal.isClosedEmbedding_coe)

theorem oldBoundaryRayMinus_isClosedEmbedding
    {b : ℝ → ℂ} (hb : IsClosedEmbedding b) (c : ℝ) :
    IsClosedEmbedding (oldBoundaryRayMinus b c) := by
  exact hb.comp ((Homeomorph.subLeft c).isClosedEmbedding.comp
    NNReal.isClosedEmbedding_coe)

theorem oldBoundaryRayPlus_range (b : ℝ → ℂ) (c : ℝ) :
    range (oldBoundaryRayPlus b c) = b '' Ici c := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨c + (u : ℝ), le_add_of_nonneg_right u.prop, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v - c, sub_nonneg.mpr hv⟩, ?_⟩
    change b (c + (v - c)) = b v
    congr 1
    ring

theorem oldBoundaryRayMinus_range (b : ℝ → ℂ) (c : ℝ) :
    range (oldBoundaryRayMinus b c) = b '' Iic c := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨c - (u : ℝ), sub_le_self c u.prop, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨c - v, sub_nonneg.mpr hv⟩, ?_⟩
    change b (c - (c - v)) = b v
    congr 1
    ring

/-- Pure carrier arithmetic once the removed clock range has been proved. -/
theorem oldBoundary_complement_Ici
    {b : ℝ → ℂ} (hbi : Function.Injective b) {S : Set ℂ} {c : ℝ}
    (hremoved : S ∩ range b = b '' Ici c) :
    b '' Iic c = insert (b c) (range b \ S) ∧
      (b '' Iic c) ∩ S = {b c} := by
  have hcS : b c ∈ S := (hremoved.symm ▸
    (show b c ∈ b '' Ici c from ⟨c, by simp, rfl⟩)).1
  have hcarrier : b '' Iic c = insert (b c) (range b \ S) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases huc : u = c
      · exact Or.inl (congrArg b huc)
      · right
        refine ⟨mem_range_self u, ?_⟩
        intro huS
        have huimage : b u ∈ b '' Ici c := by
          rw [← hremoved]
          exact ⟨huS, mem_range_self u⟩
        obtain ⟨v, hv, hvu⟩ := huimage
        have hcu : c ≤ u := by
          simpa only [hbi hvu] using (show c ≤ v from hv)
        exact huc (le_antisymm hu hcu)
    · rintro (hxc | ⟨⟨u, rfl⟩, huS⟩)
      · rw [hxc]
        exact ⟨c, by simp, rfl⟩
      · refine ⟨u, ?_, rfl⟩
        by_contra hcu
        have hu : u ∈ Ici c := by
          change c ≤ u
          exact le_of_not_ge hcu
        exact huS (hremoved.symm ▸ (show b u ∈ b '' Ici c from ⟨u, hu, rfl⟩)).1
  refine ⟨hcarrier, ?_⟩
  rw [hcarrier]
  ext x
  constructor
  · rintro ⟨hxc | hx, hxS⟩
    · exact hxc
    · exact False.elim (hx.2 hxS)
  · intro hxc
    have he : x = b c := hxc
    subst x
    exact ⟨Or.inl rfl, hcS⟩

theorem oldBoundary_complement_Iic
    {b : ℝ → ℂ} (hbi : Function.Injective b) {S : Set ℂ} {c : ℝ}
    (hremoved : S ∩ range b = b '' Iic c) :
    b '' Ici c = insert (b c) (range b \ S) ∧
      (b '' Ici c) ∩ S = {b c} := by
  have hcS : b c ∈ S := (hremoved.symm ▸
    (show b c ∈ b '' Iic c from ⟨c, by simp, rfl⟩)).1
  have hcarrier : b '' Ici c = insert (b c) (range b \ S) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases huc : u = c
      · exact Or.inl (congrArg b huc)
      · right
        refine ⟨mem_range_self u, ?_⟩
        intro huS
        have huimage : b u ∈ b '' Iic c := by
          rw [← hremoved]
          exact ⟨huS, mem_range_self u⟩
        obtain ⟨v, hv, hvu⟩ := huimage
        have huc' : u ≤ c := by
          simpa only [hbi hvu] using (show v ≤ c from hv)
        exact huc (le_antisymm huc' hu)
    · rintro (hxc | ⟨⟨u, rfl⟩, huS⟩)
      · rw [hxc]
        exact ⟨c, by simp, rfl⟩
      · refine ⟨u, ?_, rfl⟩
        by_contra huc
        have hu : u ∈ Iic c := by
          change u ≤ c
          exact le_of_not_ge huc
        exact huS (hremoved.symm ▸ (show b u ∈ b '' Iic c from ⟨u, hu, rfl⟩)).1
  refine ⟨hcarrier, ?_⟩
  rw [hcarrier]
  ext x
  constructor
  · rintro ⟨hxc | hx, hxS⟩
    · exact hxc
    · exact False.elim (hx.2 hxS)
  · intro hxc
    have he : x = b c := hxc
    subst x
    exact ⟨Or.inl rfl, hcS⟩

/-- Reusable boundary-clock bridge. The supplied clock merely factors the
actual removed ray through an actual closed embedded full boundary. Its
properness, orientation, and complete halfline range are all derived. -/
theorem exists_oldBoundary_complement_ray_of_clock
    {b : ℝ → ℂ} (hb : IsClosedEmbedding b)
    {δ : ℝ≥0 → ℂ} (hδ : IsClosedEmbedding δ)
    (f : ℝ≥0 → ℝ) (hfactor : ∀ u, b (f u) = δ u)
    {S : Set ℂ} (hremoved : range δ = S ∩ range b) :
    ∃ g : ℝ≥0 → ℂ, IsClosedEmbedding g ∧ g 0 = δ 0 ∧
      range g = insert (δ 0) (range b \ S) ∧ range g ∩ S = {δ 0} := by
  have hbf : b ∘ f = δ := funext hfactor
  have hf : IsClosedEmbedding f := hb.of_comp_iff.mp (hbf.symm ▸ hδ)
  have hremovedClock : S ∩ range b = b '' range f := by
    rw [← hremoved, ← range_comp, hbf]
  rcases nnreal_closedEmbedding_range_halfline hf with ⟨_, hrange⟩ | ⟨_, hrange⟩
  · rw [hrange] at hremovedClock
    obtain ⟨hcarrier, hmeet⟩ := oldBoundary_complement_Ici hb.injective hremovedClock
    refine ⟨oldBoundaryRayMinus b (f 0), oldBoundaryRayMinus_isClosedEmbedding hb _, ?_, ?_, ?_⟩
    · simpa only [oldBoundaryRayMinus_zero] using hfactor 0
    · rw [oldBoundaryRayMinus_range, hcarrier, hfactor 0]
    · rw [oldBoundaryRayMinus_range, hmeet, hfactor 0]
  · rw [hrange] at hremovedClock
    obtain ⟨hcarrier, hmeet⟩ := oldBoundary_complement_Iic hb.injective hremovedClock
    refine ⟨oldBoundaryRayPlus b (f 0), oldBoundaryRayPlus_isClosedEmbedding hb _, ?_, ?_, ?_⟩
    · simpa only [oldBoundaryRayPlus_zero] using hfactor 0
    · rw [oldBoundaryRayPlus_range, hcarrier, hfactor 0]
    · rw [oldBoundaryRayPlus_range, hmeet, hfactor 0]

/-- Application bridge for translated-strip and sector cuts. The only
normalization is the OLD ambient halfplane homeomorphism H. An actual proper
parametrization of the removed old ray plus compact edge constructs the
untouched second proper ray, including its one common endpoint.

In particular no desired residual topology, halfline carrier equality,
clock monotonicity, or parametrization of the untouched end is an input. -/
theorem exists_straightened_oldBoundary_complement_ray
    {P S : Set ℂ} (H : ℂ ≃ₜ ℂ)
    (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    {δ : ℝ≥0 → ℂ} (hδ : IsClosedEmbedding δ) {z : ℂ}
    (hδ0 : δ 0 = z) (hremoved : range δ = S ∩ frontier P) :
    ∃ g : ℝ≥0 → ℂ, IsClosedEmbedding g ∧ g 0 = z ∧
      range g = insert z (frontier P \ S) ∧ range g ∩ S = {z} := by
  have hfront : frontier P = {w : ℂ | (H w).im = 0} := by
    rw [hP, ← H.preimage_frontier]
    change H ⁻¹' frontier {w : ℂ | (0 : ℝ) ≤ w.im} = _
    rw [Complex.frontier_setOfPred_le_im]
    rfl
  let b : ℝ → ℂ := fun c => H.symm (c : ℂ)
  have hb : IsClosedEmbedding b :=
    H.symm.isClosedEmbedding.comp Complex.isometry_ofReal.isClosedEmbedding
  have hbH (w : ℂ) (hw : w ∈ frontier P) : b (H w).re = w := by
    have him : (H w).im = 0 := by
      simpa only [hfront, mem_setOf_eq] using hw
    have he : ((H w).re : ℂ) = H w := by
      apply Complex.ext <;> simp [him]
    dsimp [b]
    rw [he, H.symm_apply_apply]
  have hboundary : range b = frontier P := by
    apply Subset.antisymm
    · rintro w ⟨c, rfl⟩
      rw [hfront]
      change (H (H.symm (c : ℂ))).im = 0
      simp
    · intro w hw
      exact ⟨(H w).re, hbH w hw⟩
  let f : ℝ≥0 → ℝ := fun u => (H (δ u)).re
  have hfactor : ∀ u, b (f u) = δ u := by
    intro u
    exact hbH (δ u) ((hremoved ▸ mem_range_self u).2)
  have hremoved' : range δ = S ∩ range b := by rwa [hboundary]
  obtain ⟨g, hg, hg0, hgrange, hgmeet⟩ :=
    exists_oldBoundary_complement_ray_of_clock hb hδ f hfactor hremoved'
  refine ⟨g, hg, hg0.trans hδ0, ?_, ?_⟩
  · simpa only [hboundary, hδ0] using hgrange
  · simpa only [hδ0] using hgmeet

end RepulsiveCoulomb
