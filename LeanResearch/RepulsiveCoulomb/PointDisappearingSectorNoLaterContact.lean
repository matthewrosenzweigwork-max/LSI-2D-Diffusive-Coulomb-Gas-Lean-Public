module

public import LeanResearch.RepulsiveCoulomb.PointActualDisappearingApexReturnObstruction
public import LeanResearch.RepulsiveCoulomb.PointActualHalfDiskDepartureDirection
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexActualDeparture
public import LeanResearch.RepulsiveCoulomb.DisappearingSectorRemovedEnd
public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Original-sector adapter for the disappearing-apex
no-later-return theorem. The proper broken old end, its local halfdisk germs,
actual stopped edge, pi offset, first later contact, full-angle cap and finite
GB contradiction are constructed. No chosen cap or later-contact exclusion is
an input, and the old end is never assumed globally minimizing. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointDisappearingSector_no_later_old_contact
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P=⋃ i,range (pieces i).curve)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (hterminal : ∀ t : ℝ,(r:ℝ)<t → ¬ Icc (r:ℝ) t ⊆
      (fun u : ℝ ↦ σ (retainedApexUpperSource hβ.le hβπ u.toNNReal)) ⁻¹' frontier P)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hboundary : ν (σ (flatLinkSectorApex hβ.le))=Real.pi-β)
    (hβα : β≤α (σ (flatLinkSectorApex hβ.le)))
    (hzneg : ν (σ (retainedApexUpperSource hβ.le hβπ r))<0)
    (hνB : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-C.flatPhysicalWidth ∧ C.Admissible) :
    ∀ t : NNReal,r<t → σ (retainedApexUpperSource hβ.le hβπ t)∉frontier P := by
  let top : NNReal → ℂ:=fun t ↦ σ (retainedApexUpperSource hβ.le hβπ t)
  let ray : ℝ → ℂ:=fun t ↦ top t.toNNReal
  have htopmetric (u v : NNReal) :
      (pointSmoothConformalEDist a y (top u) (top v)).toReal=dist u v:=
    (hσ _ _).trans ((retainedApexUpperSource_isometry hβ.le hβπ).dist_eq u v)
  have htopclosed:=pointMetricRay_isClosedEmbedding ha y top htopmetric
  have hrayc : Continuous ray:=htopclosed.continuous.comp continuous_real_toNNReal
  have hraymetric : ∀ u∈Ici (0:ℝ),∀ v∈Ici (0:ℝ),
      (pointSmoothConformalEDist a y (ray u) (ray v)).toReal=dist u v:=by
    intro u hu v hv
    rw [htopmetric]
    change dist (u.toNNReal:ℝ) (v.toNNReal:ℝ)=dist u v
    rw [Real.coe_toNNReal _ hu,Real.coe_toNNReal _ hv]
  intro t hrt htfront
  have hlater : ∃ w : ℝ,(r:ℝ)<w ∧ ray w∈frontier P:=
    ⟨t,hrt,by simpa only [ray,Real.toNNReal_coe] using htfront⟩
  obtain ⟨w,hrw,hwfront,_,hgap⟩:=exists_pointMetricRay_first_later_boundary_contact
    ha y pieces hpieces ray hrayc hraymetric (NNReal.coe_nonneg r) hterminal hlater
  let d:=w-(r:ℝ)
  have hdpos : 0<d:=sub_pos.mpr hrw
  let D : NNReal:=⟨d,hdpos.le⟩
  let tail : NNReal → ℂ:=fun u ↦ top (r+u)
  let upper : ℝ → ℂ:=fun u ↦ tail u.toNNReal
  have htailmetric (u v : NNReal) :
      (pointSmoothConformalEDist a y (tail u) (tail v)).toReal=dist u v:=by
    rw [htopmetric]
    change |((r:ℝ)+(u:ℝ))-((r:ℝ)+(v:ℝ))|=|(u:ℝ)-(v:ℝ)|
    congr 1
    ring
  have htailclosed:=pointMetricRay_isClosedEmbedding ha y tail htailmetric
  have hupperc : Continuous upper:=htailclosed.continuous.comp continuous_real_toNNReal
  have huppermetric : ∀ u∈Ici (0:ℝ),∀ v∈Ici (0:ℝ),
      (pointSmoothConformalEDist a y (upper u) (upper v)).toReal=dist u v:=by
    intro u hu v hv
    rw [htailmetric]
    change dist (u.toNNReal:ℝ) (v.toNNReal:ℝ)=dist u v
    rw [Real.coe_toNNReal _ hu,Real.coe_toNNReal _ hv]
  obtain ⟨L,hL,hLr,hLsin⟩:=retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let f : flatLinkSectorDisk Real.pi L → ℂ:=σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin
  let q:=f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)
  have hqtop : q=top r:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le))=_
    rw [retainedSectorPassingHalfDisk_apex hβ hβπ hLsin hL.le (NNReal.coe_nonneg r)]
    rfl
  have htail0 : tail 0=q:=by simpa only [tail,add_zero] using hqtop.symm
  let E0:=pointMetricRaySegment ha y tail htailmetric D hdpos
  have hE00 : E0.start=q:=htail0
  let E : PointGeodesicTreeEdge a y:=
    { E0 with
      start:=q
      distinct:=fun he ↦ E0.distinct (hE00.trans he)
      curve_start:=E0.curve_start.trans hE00
      geodesic:=by intro u v; rw [← hE00]; exact E0.geodesic u v }
  have hEP : ∀ u,E.curve u∈P:=fun u ↦ hσP _
  have hElength : pointActualEdgeLength E=d:=by
    change (pointSmoothConformalEDist a y q (tail D)).toReal=d
    rw [← htail0,htailmetric,NNReal.dist_eq,NNReal.coe_zero,zero_sub,abs_neg]
    change |d| = d
    exact abs_of_pos hdpos
  have hEcurve : E.curve=lineCapSegment upper 0 d:=by
    funext u
    apply congrArg tail
    apply Subtype.ext
    change d*u.1=((0+u.1*(d-0)).toNNReal:ℝ)
    rw [sub_zero,zero_add,Real.coe_toNNReal _ (mul_nonneg u.2.1 hdpos.le)]
    ring
  have hEclock : ∀ u : unitInterval,E.curve u=upper (pointActualEdgeLength E*u.1):=by
    intro u
    rw [hElength]
    apply congrArg tail
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (mul_nonneg hdpos.le u.2.1)).symm
  have hupper0 : upper 0=E.start:=by simpa only [upper,Real.toNNReal_zero] using htail0
  have hupperD : upper d=E.finish:=by
    apply congrArg tail
    exact Subtype.ext (Real.coe_toNNReal _ hdpos.le)
  have htailD : E.finish=ray w:=by
    apply congrArg top
    apply Subtype.ext
    change (r:ℝ)+d=(w.toNNReal:ℝ)
    rw [Real.coe_toNNReal _ ((NNReal.coe_nonneg r).trans hrw.le)]
    dsimp [d]
    ring
  have hfinish : E.finish∈frontier P:=htailD.symm ▸ hwfront
  have hgapTail : ∀ u∈Ioo (0:ℝ) d,upper u∉frontier P:=by
    intro u hu
    have he : upper u=ray ((r:ℝ)+u):=by
      apply congrArg top
      apply Subtype.ext
      change (r:ℝ)+(u.toNNReal:ℝ)=(((r:ℝ)+u).toNNReal:ℝ)
      rw [Real.coe_toNNReal _ hu.1.le,Real.coe_toNNReal _ (add_nonneg (NNReal.coe_nonneg r) hu.1.le)]
    rw [he]
    apply hgap
    dsimp [d] at hu
    constructor <;> linarith [hu.1, hu.2]
  let δ : NNReal → ℂ:=σ ∘ disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r)
  let lower : ℝ → ℂ:=fun u ↦ δ u.toNNReal
  have hδclosed : IsClosedEmbedding δ:=(pointRetainedSector_closed_proper ha y hβ hβπ σ hσ).1.comp
    (disappearingSectorRemovedSource_isClosedEmbedding hβ hβπ (NNReal.coe_nonneg r))
  have hlowerc : Continuous lower:=hδclosed.continuous.comp continuous_real_toNNReal
  have hδ0 : δ 0=q:=by
    change σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) (0 : NNReal)) = q
    rw [disappearingSectorRemovedSource_zero]
    exact hqtop.symm
  have hlower0 : lower 0=E.start:=by simpa only [lower,Real.toNNReal_zero] using hδ0
  have hlowerProper : IsClosedEmbedding (fun u : NNReal ↦ lower (u:ℝ)):=by
    simpa only [lower,Real.toNNReal_coe] using hδclosed
  have hδfront (u : NNReal) : δ u∈frontier P:=by
    rcases le_total (u:ℝ) (r:ℝ) with hu | hu
    · change σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) u)∈frontier P
      rw [disappearingSectorRemovedSource_before hβ.le hβπ (NNReal.coe_nonneg r) u hu]
      exact hprefix _ (sub_le_self _ u.2)
    · change σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) u)∈frontier P
      rw [disappearingSectorRemovedSource_after hβ.le hβπ (NNReal.coe_nonneg r) u hu]
      exact hbottom _
  have hlowerfront : ∀ u∈Ici (0:ℝ),lower u∈frontier P:=fun u _ ↦ hδfront _
  have hqfront : q∈frontier P:=hqtop.symm ▸ hprefix r le_rfl
  obtain ⟨C,hνC,hC⟩:=hνB q hqfront
  have hqneg : ν E.start < 0 := by
    change ν q < 0
    rw [hqtop]
    exact hzneg
  have hremain : Real.pi<C.flatPhysicalWidth:=by linarith
  have hfmetric (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=by
    dsimp only [f, Function.comp_apply]
    rw [hσ]
    exact (retainedSectorPassingHalfDisk_isometry hβ hβπ hLsin).dist_eq x z
  have hfP : ∀ x,f x∈P:=fun x ↦ hσP _
  have hedge0 (s : ℝ) (hs : 0 ≤ s) (hsL : s≤L) :
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl s ⟨hs,hsL⟩ 0)=lower s:=by
    have hsr : s≤r:=hsL.trans hLr.le
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)=
      σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) s.toNNReal)
    rw [disappearingSectorPassing_backward hβ hβπ hLsin hs hsL hsr,
      disappearingSectorRemovedSource_before hβ.le hβπ (NNReal.coe_nonneg r) s.toNNReal
        (by rwa [Real.coe_toNNReal _ hs])]
    apply congrArg σ
    apply congrArg (retainedApexUpperSource hβ.le hβπ)
    apply Subtype.ext
    change (r : ℝ) - s = (r : ℝ) - (s.toNNReal : ℝ)
    rw [Real.coe_toNNReal _ hs]
  have hedge1 (s : ℝ) (hs : 0 ≤ s) (hsL : s≤L) :
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl s ⟨hs,hsL⟩ 1)=upper s:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)=
      σ (retainedApexUpperSource hβ.le hβπ (r+s.toNNReal))
    rw [disappearingSectorPassing_forward hβ hβπ hLsin (NNReal.coe_nonneg r) hs hsL]
    apply congrArg σ
    apply congrArg (retainedApexUpperSource hβ.le hβπ)
    apply Subtype.ext
    change (r:ℝ)+s=(r:ℝ)+(s.toNNReal:ℝ)
    rw [Real.coe_toNNReal _ hs]
  let ε:=min L (C.radius/2)
  have hε : 0<ε:=lt_min hL (half_pos C.radius_pos)
  have hεL : ε≤L:=min_le_left _ _
  have hεC : ε<C.radius:=(min_le_right _ _).trans_lt (half_lt_self C.radius_pos)
  obtain ⟨ξ,hξ,hξend,hφopen,hoccupied,hlocal⟩:=pointActualHalfDisk_construct_departure_direction
    ha y hL f hfmetric hfP C hC hremain upper lower hedge0 hedge1 E rfl hEP hEclock
    hε hεL hεC (hδfront _)
  have hreturnOutside : ∀ u∈Ici (0:ℝ),E.finish≠lower u:=by
    intro u hu he
    rw [htailD] at he
    rcases le_total (u.toNNReal:ℝ) (r:ℝ) with hur | hru
    · change ray w=σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) u.toNNReal) at he
      rw [disappearingSectorRemovedSource_before hβ.le hβπ (NNReal.coe_nonneg r) u.toNNReal hur] at he
      have heN:=htopclosed.injective he
      have heR:=congrArg (fun v : NNReal ↦ (v:ℝ)) heN
      change (w.toNNReal : ℝ) = (r : ℝ) - (u.toNNReal : ℝ) at heR
      rw [Real.coe_toNNReal _ ((NNReal.coe_nonneg r).trans hrw.le)] at heR
      linarith [NNReal.coe_nonneg u.toNNReal]
    · change ray w=σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) u.toNNReal) at he
      rw [disappearingSectorRemovedSource_after hβ.le hβπ (NNReal.coe_nonneg r) u.toNNReal hru] at he
      exact retainedApex_free_ray_avoids_bottom y hβ hβπ σ hσ w.toNNReal
        (by rw [Real.coe_toNNReal _ ((NNReal.coe_nonneg r).trans hrw.le)]; exact hr.trans hrw)
        ⟨⟨(u.toNNReal:ℝ)-(r:ℝ),sub_nonneg.mpr hru⟩,he.symm⟩
  have hpRemoved : ∃ u : ℝ,0<u ∧ lower u=σ (flatLinkSectorApex hβ.le):=by
    refine ⟨r,hr,?_⟩
    change σ (disappearingSectorRemovedSource hβ.le hβπ (NNReal.coe_nonneg r) (r:ℝ).toNNReal)=_
    rw [Real.toNNReal_coe,disappearingSectorRemovedSource_before hβ.le hβπ (NNReal.coe_nonneg r) r le_rfl]
    apply congrArg σ
    apply Subtype.ext
    change sectorPolar ((r : ℝ) - (r : ℝ)) β = 0
    rw [sub_self, sectorPolar_zero]
  have hνSimple : ∀ x∈frontier P,∃ K : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-(1+coalescedPointExponent a y x/2)*(K.hi-K.lo):=by
    intro x hx
    obtain ⟨K,hK,_⟩:=hνB x hx
    refine ⟨K, ?_⟩
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y x/2) 1] using hK
  exact not_actual_disappearing_apex_return_of_proper_old_end ha y H hHP pieces hpieces E hEP C hC hφopen
    lower upper hlowerc hupperc hlower0 hlowerProper hreturnOutside hε hξ hξend hlocal hoccupied
    hlowerfront hdpos hEcurve hupper0 hupperD
    (fun u hu v hv ↦ huppermetric u hu.1 v hv.1) hgapTail hfinish
    hbudget hνSimple hboundary hβπ hβα hqneg hpRemoved

end RepulsiveCoulomb
