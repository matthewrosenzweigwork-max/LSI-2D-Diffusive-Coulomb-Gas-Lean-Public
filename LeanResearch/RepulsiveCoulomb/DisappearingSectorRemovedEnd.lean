module

public import LeanResearch.RepulsiveCoulomb.RetainedSectorSourceTopology
public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorRelativeOpenness
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The old removed end is a proper BROKEN ray:
from the departure z backwards along the upper source edge to the original
apex, then outward along the bottom. No global metric-ray assertion is made.
An explicit continuous linear source clock proves its closed embedding. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

private theorem disappearingSector_bottom_isometry {β : ℝ} (hβ : 0≤β) (hβπ : β≤Real.pi) :
    Isometry (retainedApexBottomSource hβ hβπ) := by
  apply Isometry.of_dist_eq
  intro r s
  change dist (sectorPolar r 0) (sectorPolar s 0)=dist (r:ℝ) (s:ℝ)
  simp only [sectorPolar,conePhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  exact Complex.isometry_ofReal.dist_eq _ _

/-- Signed boundary clock functional. It is +r on the bottom and -r on the
upper edge, including beta=pi. The half-angle denominator is nonzero. -/
def disappearingSectorSignedClock (β : ℝ) (q : ℂ) : ℝ :=
  q.re-q.im*(Real.cos (β/2)/Real.sin (β/2))

theorem disappearingSectorSignedClock_bottom (β s : ℝ) :
    disappearingSectorSignedClock β (sectorPolar s 0)=s := by
  simp [disappearingSectorSignedClock,sectorPolar_re,sectorPolar_im]

theorem disappearingSectorSignedClock_upper {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (s : ℝ) : disappearingSectorSignedClock β (sectorPolar s β) = -s := by
  have hs : 0<Real.sin (β/2):=Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])
  have htrig : Real.cos β*Real.sin (β/2)-Real.sin β*Real.cos (β/2) = -Real.sin (β/2) := by
    calc
      _=Real.sin (β/2-β):=by rw [Real.sin_sub]; ring
      _ = -Real.sin (β/2):=by rw [show β/2-β= -(β/2) by ring,Real.sin_neg]
  unfold disappearingSectorSignedClock
  rw [sectorPolar_re,sectorPolar_im]
  apply (mul_right_cancel₀ hs.ne')
  field_simp [hs.ne']
  nlinarith [congrArg (fun v : ℝ ↦ s*v) htrig]

/-- Actual source path z→apex→infinity. It is generally not minimizing
between points on opposite sides of the apex. -/
def disappearingSectorRemovedSource {β r : ℝ} (hβ : 0≤β) (hβπ : β≤Real.pi)
    (hr : 0≤r) (t : NNReal) : closedEuclideanSector β :=
  ⟨sectorPolar (max (r-(t:ℝ)) 0) β+sectorPolar (max ((t:ℝ)-r) 0) 0,by
    rcases le_total (t:ℝ) r with ht | ht
    · have he : max ((t:ℝ)-r) 0=0:=max_eq_right (sub_nonpos.mpr ht)
      simp only [he,sectorPolar_zero,add_zero]
      exact (retainedApexUpperSource hβ hβπ ⟨max (r-(t:ℝ)) 0,le_max_right _ _⟩).2
    · have he : max (r-(t:ℝ)) 0=0:=max_eq_right (sub_nonpos.mpr ht)
      simp only [he,sectorPolar_zero,zero_add]
      exact (retainedApexBottomSource hβ hβπ ⟨max ((t:ℝ)-r) 0,le_max_right _ _⟩).2⟩

theorem disappearingSectorRemovedSource_before {β r : ℝ} (hβ : 0≤β)
    (hβπ : β≤Real.pi) (hr : 0≤r) (t : NNReal) (ht : (t:ℝ)≤r) :
    disappearingSectorRemovedSource hβ hβπ hr t=
      retainedApexUpperSource hβ hβπ ⟨r-(t:ℝ),sub_nonneg.mpr ht⟩ := by
  apply Subtype.ext
  simp [disappearingSectorRemovedSource,retainedApexUpperSource,
    max_eq_left (sub_nonneg.mpr ht),max_eq_right (sub_nonpos.mpr ht),sectorPolar_zero] <;> rfl

theorem disappearingSectorRemovedSource_after {β r : ℝ} (hβ : 0≤β)
    (hβπ : β≤Real.pi) (hr : 0≤r) (t : NNReal) (ht : r≤(t:ℝ)) :
    disappearingSectorRemovedSource hβ hβπ hr t=
      retainedApexBottomSource hβ hβπ ⟨(t:ℝ)-r,sub_nonneg.mpr ht⟩ := by
  apply Subtype.ext
  simp [disappearingSectorRemovedSource,retainedApexBottomSource,
    max_eq_right (sub_nonpos.mpr ht),max_eq_left (sub_nonneg.mpr ht),sectorPolar_zero] <;> rfl

@[simp] theorem disappearingSectorRemovedSource_zero {β r : ℝ} (hβ : 0≤β)
    (hβπ : β≤Real.pi) (hr : 0≤r) :
    disappearingSectorRemovedSource hβ hβπ hr 0=
      retainedApexUpperSource hβ hβπ ⟨r,hr⟩ := by
  rw [disappearingSectorRemovedSource_before hβ hβπ hr 0 hr]
  congr 1
  apply Subtype.ext
  simp

theorem disappearingSectorRemovedSource_range {β r : ℝ} (hβ : 0≤β)
    (hβπ : β≤Real.pi) (hr : 0≤r) :
    range (disappearingSectorRemovedSource hβ hβπ hr)=
      range (retainedApexBottomSource hβ hβπ) ∪
      retainedApexUpperSource hβ hβπ '' Icc 0 (⟨r,hr⟩:NNReal) := by
  ext q
  constructor
  · rintro ⟨t,rfl⟩
    rcases le_total (t:ℝ) r with ht | ht
    · right
      refine ⟨⟨r-(t:ℝ),sub_nonneg.mpr ht⟩,⟨zero_le,?_⟩,
        (disappearingSectorRemovedSource_before hβ hβπ hr t ht).symm⟩
      change r-(t:ℝ)≤r
      exact sub_le_self _ t.2
    · left
      exact ⟨⟨(t:ℝ)-r,sub_nonneg.mpr ht⟩,
        (disappearingSectorRemovedSource_after hβ hβπ hr t ht).symm⟩
  · rintro (⟨s,rfl⟩ | ⟨s,hs,rfl⟩)
    · let t : NNReal:=⟨r+(s:ℝ),add_nonneg hr s.2⟩
      refine ⟨t,?_⟩
      rw [disappearingSectorRemovedSource_after hβ hβπ hr t (by change r≤r+(s:ℝ); linarith [s.2])]
      congr 1
      apply Subtype.ext
      change r+(s:ℝ)-r=s
      ring
    · let t : NNReal:=⟨r-(s:ℝ),sub_nonneg.mpr hs.2⟩
      refine ⟨t,?_⟩
      rw [disappearingSectorRemovedSource_before hβ hβπ hr t (by change r-(s:ℝ)≤r; exact sub_le_self _ s.2)]
      congr 1
      apply Subtype.ext
      change r-(r-(s:ℝ))=s
      ring

/-- Constructed closed embedding of the removed source path. The proof uses a
continuous LEFT INVERSE, not a false pair-distance formula across its corner. -/
theorem disappearingSectorRemovedSource_isClosedEmbedding {β r : ℝ}
    (hβ : 0<β) (hβπ : β≤Real.pi) (hr : 0≤r) :
    IsClosedEmbedding (disappearingSectorRemovedSource hβ.le hβπ hr) := by
  let clock : closedEuclideanSector β → NNReal:=fun q ↦
    (r+disappearingSectorSignedClock β q.1).toNNReal
  have hc : Continuous (disappearingSectorRemovedSource hβ.le hβπ hr):=by
    apply Continuous.subtype_mk
    unfold sectorPolar conePhase
    fun_prop
  have hclock : Continuous clock:=by
    unfold clock disappearingSectorSignedClock
    fun_prop
  have hleft : Function.LeftInverse clock (disappearingSectorRemovedSource hβ.le hβπ hr):=by
    intro t
    rcases le_total (t:ℝ) r with ht | ht
    · rw [disappearingSectorRemovedSource_before hβ.le hβπ hr t ht]
      change (r+disappearingSectorSignedClock β (sectorPolar (r-(t:ℝ)) β)).toNNReal=t
      rw [disappearingSectorSignedClock_upper hβ hβπ]
      simp only [show r+ -(r-(t:ℝ))=(t:ℝ) by ring,Real.toNNReal_coe]
    · rw [disappearingSectorRemovedSource_after hβ.le hβπ hr t ht]
      change (r+disappearingSectorSignedClock β (sectorPolar ((t:ℝ)-r) 0)).toNNReal=t
      rw [disappearingSectorSignedClock_bottom]
      simp only [show r+((t:ℝ)-r)=(t:ℝ) by ring,Real.toNNReal_coe]
  have hclosed : IsClosed (range (disappearingSectorRemovedSource hβ.le hβπ hr)):=by
    rw [disappearingSectorRemovedSource_range hβ.le hβπ hr]
    exact (disappearingSector_bottom_isometry hβ.le hβπ).isClosedEmbedding.isClosed_range.union
      (isCompact_Icc.image (retainedApexUpperSource_isometry hβ.le hβπ).continuous).isClosed
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap hc hleft.injective
  intro A hA
  have he : disappearingSectorRemovedSource hβ.le hβπ hr '' A=
      range (disappearingSectorRemovedSource hβ.le hβπ hr) ∩ clock ⁻¹' A:=by
    ext q
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨mem_range_self t,by simpa only [mem_preimage,hleft t] using ht⟩
    · rintro ⟨⟨t,rfl⟩,ht⟩
      exact ⟨t,by simpa only [mem_preimage,hleft t] using ht,rfl⟩
  rw [he]
  exact hclosed.inter (hA.preimage hclock)

/-- Proper old-end escape needed by the two-arc full-angle cap constructor.
A closed embedded ray suffices; no global minimization/speed condition occurs. -/
theorem closedEmbedding_nnreal_positive_escape {δ : NNReal → ℂ}
    (hδ : IsClosedEmbedding δ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ t : NNReal,0<t ∧ δ t∉K := by
  obtain ⟨M,hM⟩:=(hδ.isProperMap.isCompact_preimage hK).bddAbove
  let t : NNReal:=M+1
  have ht : 0<t:=by dsimp [t]; positivity
  refine ⟨t,ht,?_⟩
  intro htK
  have hle : t≤M:=hM htK
  dsimp [t] at hle
  have hp : (0:NNReal)<1:=by norm_num
  exact (not_le_of_gt (lt_add_of_pos_right M hp)) hle

/-- The original actual sector creates the proper broken target old-end.
Its boundary membership is obtained once the initial upper contact interval
has been CONSTRUCTED; no assertion about later contact appears in this lemma. -/
theorem pointDisappearingSector_actual_removed_end
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β r : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi) (hr : 0≤r)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ}
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (hprefix : ∀ t : NNReal,(t:ℝ)≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P) :
    ∃ δ : NNReal → ℂ,IsClosedEmbedding δ ∧
      δ 0=σ (retainedApexUpperSource hβ.le hβπ ⟨r,hr⟩) ∧
      range δ=range (fun t : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ t)) ∪
        (fun t : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ t)) '' Icc 0 ⟨r,hr⟩ ∧
      (∀ t,δ t∈frontier P) ∧
      (∀ K : Set ℂ,IsCompact K → ∃ t : NNReal,0<t ∧ δ t∉K) := by
  let δ:=σ ∘ disappearingSectorRemovedSource hβ.le hβπ hr
  have hδ : IsClosedEmbedding δ:=(pointRetainedSector_closed_proper ha y hβ hβπ σ hσ).1.comp
    (disappearingSectorRemovedSource_isClosedEmbedding hβ hβπ hr)
  have hδrange : range δ=
      range (fun t : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ t)) ∪
      (fun t : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ t)) '' Icc 0 ⟨r,hr⟩:=by
    rw [range_comp,disappearingSectorRemovedSource_range hβ.le hβπ hr,
      image_union,← range_comp,image_image]
    rfl
  refine ⟨δ,hδ,by simp [δ],hδrange,?_,closedEmbedding_nnreal_positive_escape hδ⟩
  intro t
  have ht:=hδrange ▸ mem_range_self t
  rcases ht with ⟨u,hu⟩ | ⟨u,hu,he⟩
  · exact hu ▸ hbottom u
  · exact he ▸ hprefix u hu.2

end RepulsiveCoulomb
