import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfplaneHomeomorphisms
import Mathlib.Topology.Order.OrderClosed

/-! NEW SOURCE-ONLY, UNCOMPILED DRAFT. A bent replacement boundary is not a
metric line. This module constructs its proper embedding and Schoenflies sides
from its two actual closed embedded rays. No residual homeomorphism is input. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def planarTwoRayJoin (f g : NNReal → ℂ) (s : ℝ) : ℂ :=
  if s ≤ 0 then f ((-s).toNNReal) else g (s.toNNReal)

@[simp] theorem planarTwoRayJoin_nonpos (f g : NNReal → ℂ) (r : NNReal) :
    planarTwoRayJoin f g (-(r : ℝ)) = f r := by
  simp [planarTwoRayJoin, neg_nonpos.mpr r.2]

@[simp] theorem planarTwoRayJoin_nonneg {f g : NNReal → ℂ}
    (hzero : f 0 = g 0) (r : NNReal) :
    planarTwoRayJoin f g (r : ℝ) = g r := by
  by_cases hr : r = 0
  · subst r
    simpa [planarTwoRayJoin] using hzero
  · have hp : 0 < (r : ℝ) := by
      exact lt_of_le_of_ne r.2 (fun he ↦ hr (Subtype.ext he.symm))
    simp [planarTwoRayJoin, not_le.mpr hp]

theorem planarTwoRayJoin_continuous {f g : NNReal → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hzero : f 0 = g 0) :
    Continuous (planarTwoRayJoin f g) := by
  apply Continuous.if_le
    (hf.comp (continuous_real_toNNReal.comp continuous_neg))
    (hg.comp continuous_real_toNNReal) continuous_id continuous_const
  intro s hs
  change s = 0 at hs
  subst s
  simpa using hzero

theorem planarTwoRayJoin_cross_eq_zero {f g : NNReal → ℂ}
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hzero : f 0 = g 0) (hmeet : range f ∩ range g = {f 0})
    {r u : NNReal} (h : f r = g u) : r = 0 ∧ u = 0 := by
  have hfr : f r = f 0 := mem_singleton_iff.mp
    (hmeet ▸ And.intro (mem_range_self r) ⟨u, h.symm⟩)
  exact ⟨hfi hfr, hgi (h.symm.trans (hfr.trans hzero))⟩

theorem planarTwoRayJoin_injective {f g : NNReal → ℂ}
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hzero : f 0 = g 0) (hmeet : range f ∩ range g = {f 0}) :
    Function.Injective (planarTwoRayJoin f g) := by
  intro s u h
  by_cases hs : s ≤ 0 <;> by_cases hu : u ≤ 0
  · simp only [planarTwoRayJoin, if_pos hs, if_pos hu] at h
    have he := congrArg (fun r : NNReal ↦ (r : ℝ)) (hfi h)
    rw [Real.coe_toNNReal _ (neg_nonneg.mpr hs),
      Real.coe_toNNReal _ (neg_nonneg.mpr hu)] at he
    linarith
  · simp only [planarTwoRayJoin, if_pos hs, if_neg hu] at h
    obtain ⟨hr, ht⟩ := planarTwoRayJoin_cross_eq_zero hfi hgi hzero hmeet h
    have hr' := congrArg (fun r : NNReal ↦ (r : ℝ)) hr
    have ht' := congrArg (fun r : NNReal ↦ (r : ℝ)) ht
    rw [Real.coe_toNNReal _ (neg_nonneg.mpr hs)] at hr'
    rw [Real.coe_toNNReal _ (le_of_lt (lt_of_not_ge hu))] at ht'
    norm_num at hr' ht'
    linarith
  · simp only [planarTwoRayJoin, if_neg hs, if_pos hu] at h
    obtain ⟨hr, ht⟩ := planarTwoRayJoin_cross_eq_zero hfi hgi hzero hmeet h.symm
    have hr' := congrArg (fun r : NNReal ↦ (r : ℝ)) hr
    have ht' := congrArg (fun r : NNReal ↦ (r : ℝ)) ht
    rw [Real.coe_toNNReal _ (neg_nonneg.mpr hu)] at hr'
    rw [Real.coe_toNNReal _ (le_of_lt (lt_of_not_ge hs))] at ht'
    norm_num at hr' ht'
    linarith
  · simp only [planarTwoRayJoin, if_neg hs, if_neg hu] at h
    have he := congrArg (fun r : NNReal ↦ (r : ℝ)) (hgi h)
    rw [Real.coe_toNNReal _ (le_of_lt (lt_of_not_ge hs)),
      Real.coe_toNNReal _ (le_of_lt (lt_of_not_ge hu))] at he
    exact he

theorem planarTwoRayJoin_image {f g : NNReal → ℂ}
    (hzero : f 0 = g 0) (A : Set ℝ) :
    planarTwoRayJoin f g '' A =
      f '' {r : NNReal | -(r : ℝ) ∈ A} ∪ g '' {r : NNReal | (r : ℝ) ∈ A} := by
  ext z
  constructor
  · rintro ⟨s, hsA, rfl⟩
    by_cases hs : s ≤ 0
    · refine Or.inl ⟨(-s).toNNReal, ?_, ?_⟩
      · change -(((-s).toNNReal : NNReal) : ℝ) ∈ A
        rwa [Real.coe_toNNReal _ (neg_nonneg.mpr hs), neg_neg]
      · simp [planarTwoRayJoin, hs]
    · refine Or.inr ⟨s.toNNReal, ?_, ?_⟩
      · change ((s.toNNReal : NNReal) : ℝ) ∈ A
        rwa [Real.coe_toNNReal _ (le_of_lt (lt_of_not_ge hs))]
      · simp [planarTwoRayJoin, hs]
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨-(r : ℝ), hr, planarTwoRayJoin_nonpos f g r⟩
    · exact ⟨(r : ℝ), hr, planarTwoRayJoin_nonneg hzero r⟩

theorem planarTwoRayJoin_range {f g : NNReal → ℂ} (hzero : f 0 = g 0) :
    range (planarTwoRayJoin f g) = range f ∪ range g := by
  simpa using planarTwoRayJoin_image hzero (univ : Set ℝ)

/-- The glued line's closed embedding is PROVED from those of the rays. -/
theorem planarTwoRayJoin_isClosedEmbedding {f g : NNReal → ℂ}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (hzero : f 0 = g 0) (hmeet : range f ∩ range g = {f 0}) :
    IsClosedEmbedding (planarTwoRayJoin f g) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (planarTwoRayJoin_continuous hf.continuous hg.continuous hzero)
    (planarTwoRayJoin_injective hf.injective hg.injective hzero hmeet)
  intro A hA
  rw [planarTwoRayJoin_image hzero A]
  exact (hf.isClosedMap _ (hA.preimage continuous_subtype_val.neg)).union
    (hg.isClosedMap _ (hA.preimage continuous_subtype_val))

/-- Actual Jordan compactification of the two-ray replacement line. This
copies the two-arc argument at its correct topological generality. -/
theorem planarTwoRayJoin_inverted_jordan {f g : NNReal → ℂ}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (hzero : f 0 = g 0) (hmeet : range f ∩ range g = {f 0})
    {p : ℂ} (hp : p ∉ range (planarTwoRayJoin f g)) :
    Schoenflies.IsJordanCurve
      (Complex.orthonormalBasisOneI.repr ''
        insert 0 (planarInversion p '' range (planarTwoRayJoin f g))) := by
  have hrange := planarTwoRayJoin_range hzero
  have hpf : p ∉ range f := fun h ↦ hp (hrange.symm ▸ Or.inl h)
  have hpg : p ∉ range g := fun h ↦ hp (hrange.symm ▸ Or.inr h)
  let F := compactifiedPlanarRay p f
  let G := compactifiedPlanarRay p g
  have hF := compactifiedPlanarRay_isClosedEmbedding hf hpf
  have hG := compactifiedPlanarRay_isClosedEmbedding hg hpg
  have hF0 : F ⟨0, by norm_num⟩ = planarInversion p (f 0) := compactifiedPlanarRay_zero p f
  have hG0 : G ⟨0, by norm_num⟩ = planarInversion p (f 0) := by
    change compactifiedPlanarRay p g 0 = planarInversion p (f 0)
    rw [compactifiedPlanarRay_zero, hzero]
  have hF1 : F ⟨1, by norm_num⟩ = 0 := compactifiedPlanarRay_one p f
  have hG1 : G ⟨1, by norm_num⟩ = 0 := compactifiedPlanarRay_one p g
  have hFG : range F ∩ range G = {planarInversion p (f 0), 0} :=
    compactifiedPlanarRay_pair_intersection rfl hzero.symm hmeet
  let e := Complex.orthonormalBasisOneI.repr
  have hFA := isArcBetween_of_continuous_injective_interval (e ∘ F)
    (e.continuous.comp hF.continuous) (e.injective.comp hF.injective)
  have hGA := isArcBetween_of_continuous_injective_interval (e ∘ G)
    (e.continuous.comp hG.continuous) (e.injective.comp hG.injective)
  simp only [Function.comp_apply, hF0, hG0, hF1, hG1] at hFA hGA
  have hintersection : range (e ∘ F) ∩ range (e ∘ G) =
      {e (planarInversion p (f 0)), e 0} := by
    rw [range_comp, range_comp, ← image_inter e.injective, hFG,
      image_insert_eq, image_singleton]
  have hJ := Schoenflies.IsJordanCurve.two_arcs_of_two_arcs hFA hGA hintersection
  have hcarrier : range F ∪ range G =
      insert 0 (planarInversion p '' range (planarTwoRayJoin f g)) := by
    rw [range_compactifiedPlanarRay, range_compactifiedPlanarRay,
      insert_union, union_insert, insert_idem, ← image_union, hrange]
  rw [range_comp, range_comp, ← image_union, hcarrier] at hJ
  exact hJ

/-- A chosen point outside the actual joined rays fixes the removed side.
Neither a straightening nor either side is an assumption. -/
theorem exists_planarTwoRayJoin_halfplaneHomeomorphs_positive_at
    {f g : NNReal → ℂ} (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g)
    (hzero : f 0 = g 0) (hmeet : range f ∩ range g = {f 0})
    {p : ℂ} (hp : p ∉ range (planarTwoRayJoin f g)) :
    ∃ D : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin f g), p ∈ D.positive := by
  have hj := planarTwoRayJoin_isClosedEmbedding hf hg hzero hmeet
  have hk : IsClosedEmbedding (fun t : ℝ ↦ (t : ℂ)) :=
    Complex.isometry_ofReal.isClosedEmbedding
  have hq : Complex.I ∉ range (fun t : ℝ ↦ (t : ℂ)) := by
    rintro ⟨t, ht⟩
    have hi := congrArg Complex.im ht
    simpa using hi
  obtain ⟨F, hF0, hF⟩ := exists_pointedPlanarLine_extension hj hk hp hq
    (planarTwoRayJoin_inverted_jordan hf hg hzero hmeet hp)
  let H := planarInversionConjugateHomeomorph F hF0 p Complex.I
  have hHp : H p = Complex.I := by
    simp [H, planarInversionConjugateHomeomorph_apply, planarInversion, hF0]
  have hH : ∀ t : ℝ, H (planarTwoRayJoin f g t) = (t : ℂ) := by
    intro t
    rw [planarInversionConjugateHomeomorph_apply, hF]
    simp [planarInversion]
  let D := lineHalfplaneHomeomorphs_of_straightening H hH
  refine ⟨D, ?_⟩
  rw [D.positive_eq]
  change 0 < (H p).im
  rw [hHp]
  simp

end RepulsiveCoulomb
