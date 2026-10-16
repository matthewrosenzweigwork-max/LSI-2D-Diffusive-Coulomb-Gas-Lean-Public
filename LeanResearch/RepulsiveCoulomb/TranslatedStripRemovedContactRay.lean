module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripSourceGeometry

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. The removed old boundary is an ACTUAL proper
ray starting at z: first the compact edge backwards to p, then the bottom ray.
Its closed embedding and carrier are proved from an explicit source clock. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def translatedStripRemovedContactSource {v : ℂ} {b : ℝ} (hb : 0≤b) (t : NNReal) :
    flatShearedStrip v b :=
  ⟨flatShearedPoint v (max ((t:ℝ)-b) 0) (max (b-(t:ℝ)) 0),
    max ((t:ℝ)-b) 0,le_max_right _ _,max (b-(t:ℝ)) 0,
    ⟨le_max_right _ _,max_le (sub_le_self _ t.2) hb⟩,rfl⟩

@[simp] theorem translatedStripRemovedContactSource_zero {v : ℂ} {b : ℝ} (hb : 0≤b) :
    translatedStripRemovedContactSource (v:=v) hb 0=translatedStripTop hb 0 := by
  apply Subtype.ext
  simp [translatedStripRemovedContactSource,translatedStripTop,hb,neg_nonpos.mpr hb]

theorem translatedStripRemovedContactSource_before {v : ℂ} {b : ℝ} (hb : 0≤b)
    (t : NNReal) (ht : (t:ℝ)≤b) :
    translatedStripRemovedContactSource (v:=v) hb t=
      translatedStripEdge (⟨b-(t:ℝ),sub_nonneg.mpr ht,sub_le_self _ t.2⟩ : Icc (0:ℝ) b) := by
  apply Subtype.ext
  simp only [translatedStripRemovedContactSource,translatedStripEdge,
    max_eq_right (sub_nonpos.mpr ht),max_eq_left (sub_nonneg.mpr ht)]

theorem translatedStripRemovedContactSource_after {v : ℂ} {b : ℝ} (hb : 0≤b)
    (t : NNReal) (ht : b≤(t:ℝ)) :
    translatedStripRemovedContactSource (v:=v) hb t=
      translatedStripBottom hb (⟨(t:ℝ)-b,sub_nonneg.mpr ht⟩ : NNReal) := by
  apply Subtype.ext
  change flatShearedPoint v (max ((t : ℝ) - b) 0) (max (b - (t : ℝ)) 0) =
    flatShearedPoint v ((t : ℝ) - b) 0
  rw [max_eq_left (sub_nonneg.mpr ht), max_eq_right (sub_nonpos.mpr ht)]

theorem translatedStripRemovedContactSource_range {v : ℂ} {b : ℝ} (hb : 0≤b) :
    range (translatedStripRemovedContactSource (v:=v) hb)=
      range (translatedStripBottom hb) ∪ range (@translatedStripEdge v b) := by
  ext q
  constructor
  · rintro ⟨t,rfl⟩
    rcases le_total (t:ℝ) b with ht | ht
    · right
      exact ⟨⟨b-(t:ℝ),sub_nonneg.mpr ht,sub_le_self _ t.2⟩,
        (translatedStripRemovedContactSource_before hb t ht).symm⟩
    · left
      exact ⟨⟨(t:ℝ)-b,sub_nonneg.mpr ht⟩,
        (translatedStripRemovedContactSource_after hb t ht).symm⟩
  · rintro (⟨r,rfl⟩ | ⟨u,rfl⟩)
    · let t : NNReal:=⟨b+(r:ℝ),add_nonneg hb r.2⟩
      refine ⟨t,?_⟩
      rw [translatedStripRemovedContactSource_after hb t (by change b≤b+(r:ℝ); linarith [r.2])]
      apply congrArg (translatedStripBottom hb)
      apply Subtype.ext
      change b+(r:ℝ)-b=r
      ring
    · let t : NNReal:=⟨b-u.1,sub_nonneg.mpr u.2.2⟩
      refine ⟨t,?_⟩
      rw [translatedStripRemovedContactSource_before hb t (by change b-u.1≤b; exact sub_le_self _ u.2.1)]
      apply congrArg (@translatedStripEdge v b)
      apply Subtype.ext
      change b-(b-u.1)=u.1
      ring

def translatedStripRemovedContactClock {v : ℂ} {b : ℝ} (hvi : v.im≠0)
    (q : flatShearedStrip v b) : NNReal :=
  (((flatShearHomeomorph hvi).symm q.1).1+b-
    ((flatShearHomeomorph hvi).symm q.1).2).toNNReal

theorem translatedStripRemovedContactClock_leftInverse {v : ℂ} {b : ℝ}
    (hvi : v.im≠0) (hb : 0≤b) :
    Function.LeftInverse (translatedStripRemovedContactClock (b:=b) hvi)
      (translatedStripRemovedContactSource (v:=v) hb) := by
  intro t
  change Real.toNNReal
    (((flatShearHomeomorph hvi).symm ((flatShearHomeomorph hvi)
      (max ((t:ℝ)-b) 0,max (b-(t:ℝ)) 0))).1+b-
      ((flatShearHomeomorph hvi).symm ((flatShearHomeomorph hvi)
        (max ((t:ℝ)-b) 0,max (b-(t:ℝ)) 0))).2)=t
  simp only [(flatShearHomeomorph hvi).symm_apply_apply]
  have he : max ((t:ℝ)-b) 0+b-max (b-(t:ℝ)) 0=(t:ℝ) := by
    rcases le_total (t:ℝ) b with ht | ht
    · rw [max_eq_right (sub_nonpos.mpr ht),max_eq_left (sub_nonneg.mpr ht)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr ht),max_eq_right (sub_nonpos.mpr ht)]
      ring
  rw [he]
  simp

theorem translatedStripRemovedContactSource_isClosedEmbedding {v : ℂ} {b : ℝ}
    (hvi : v.im≠0) (hb : 0≤b) :
    IsClosedEmbedding (translatedStripRemovedContactSource (v:=v) hb) := by
  have hc : Continuous (translatedStripRemovedContactSource (v:=v) hb) := by
    apply Continuous.subtype_mk
    unfold flatShearedPoint
    fun_prop
  have hclock : Continuous (translatedStripRemovedContactClock (b:=b) hvi) := by
    unfold translatedStripRemovedContactClock
    fun_prop
  have hleft:=translatedStripRemovedContactClock_leftInverse hvi hb
  have hclosed : IsClosed (range (translatedStripRemovedContactSource (v:=v) hb)) := by
    rw [translatedStripRemovedContactSource_range hb]
    have hbottom := (translatedStripBottom_isometry (v:=v) hb).isClosedEmbedding.isClosed_range
    have hedgeCont : Continuous (@translatedStripEdge v b) := by
      apply Continuous.subtype_mk
      unfold flatShearedPoint
      fun_prop
    exact hbottom.union (isCompact_range hedgeCont).isClosed
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap hc hleft.injective
  intro A hA
  have he : translatedStripRemovedContactSource (v:=v) hb '' A=
      range (translatedStripRemovedContactSource (v:=v) hb) ∩
        (translatedStripRemovedContactClock (b:=b) hvi) ⁻¹' A := by
    ext q
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨mem_range_self t,by simpa only [mem_preimage, hleft t] using ht⟩
    · rintro ⟨⟨t,rfl⟩,ht⟩
      exact ⟨t,by simpa only [mem_preimage, hleft t] using ht,rfl⟩
  rw [he]
  exact hclosed.inter (hA.preimage hclock)

/-- Compose the explicit source ray with the actual strip isometry. Its image
is exactly the removed old-boundary contact, and its initial point is z. -/
theorem pointTranslatedStrip_removed_contact_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P=
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1)) :
    ∃ δ : NNReal→ℂ,IsClosedEmbedding δ ∧
      δ 0=(F (translatedStripTop hb.le 0)).1 ∧
      range δ=range (fun x ↦ (F x).1) ∩ frontier P := by
  have hvi : (conePhase stripAngle).im≠0:=by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  have hc:=(pointTranslatedStrip_closed_proper ha y hvi F hF).1
  let δ : NNReal→ℂ:=fun t ↦ (F (translatedStripRemovedContactSource hb.le t)).1
  refine ⟨δ,hc.comp (translatedStripRemovedContactSource_isClosedEmbedding hvi hb.le),?_,?_⟩
  · exact congrArg (fun x ↦ (F x).1) (translatedStripRemovedContactSource_zero hb.le)
  · change range ((fun x ↦ (F x).1) ∘ translatedStripRemovedContactSource hb.le)=_
    rw [range_comp,translatedStripRemovedContactSource_range hb.le,image_union,
      ← range_comp,← range_comp,hcontact]
    rfl

end RepulsiveCoulomb
