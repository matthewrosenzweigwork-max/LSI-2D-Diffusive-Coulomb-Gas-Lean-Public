module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRemovedBoundary
public import LeanResearch.RepulsiveCoulomb.MetricFullStripLocalFullness
public import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Relative openness of the actual strip below
its top is derived, including the removed apex and compact edge. Boundary
fullness comes from actual interval filling. Clean interior points use genuine
whole Euclidean disk charts and Euclidean isometry rigidity. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_without_top_relatively_open
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (hcharts : ∀ p∈frontier P,∃ C : PointRetainedConeNeighborhood a y P p,C.Admissible)
    (hcleanInterior : ∀ p∈interior P,
      p∈range (fun x ↦ (F x).1) \ range (fun r ↦ (F (translatedStripTop hb.le r)).1) →
        coalescedPointExponent a y p=0) :
    IsOpen {z : P | z.1∈range (fun x ↦ (F x).1) \
      range (fun r ↦ (F (translatedStripTop hb.le r)).1)} := by
  have hs:=Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  have hvi : (conePhase stripAngle).im≠0:=by rw [conePhase_im]; exact hs.ne'
  have hbottom (r : NNReal) : (F (translatedStripBottom hb.le r)).1∈frontier P := by
    have hm : (F (translatedStripBottom hb.le r)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inl ⟨r,rfl⟩
    exact hm.2
  have hedge (u : Icc (0:ℝ) b) : (F (translatedStripEdge u)).1∈frontier P := by
    have hm : (F (translatedStripEdge u)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inr ⟨u,rfl⟩
    exact hm.2
  let M:=pointRegionMetricSpace ha y P
  letI : MetricSpace P:=M
  letI : PseudoMetricSpace P:=M.toPseudoMetricSpace
  letI : EMetricSpace P:=M.toEMetricSpace
  letI : PseudoEMetricSpace P:=M.toPseudoEMetricSpace
  letI : UniformSpace P:=M.toUniformSpace
  letI : TopologicalSpace P:=M.toUniformSpace.toTopologicalSpace
  have hFi : @Isometry (flatShearedStrip (conePhase stripAngle) b) P inferInstance M.toPseudoEMetricSpace F:=
    Isometry.of_dist_eq hF
  have hFval : Function.Injective (fun x ↦ (F x).1):=
    fun x z he ↦ hFi.injective (Subtype.ext he)
  have htopclosed : IsClosed (range (F ∘ translatedStripTop hb.le)):=
    (hFi.comp (translatedStripTop_isometry hb.le)).isClosedEmbedding.isClosed_range
  have ho : IsOpen (range F \ range (F ∘ translatedStripTop hb.le)):=by
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨⟨q,rfl⟩,hqnot⟩
    have hqtop : (F q).1∉range (fun r ↦ (F (translatedStripTop hb.le r)).1):=by
      rintro ⟨r,hr⟩
      exact hqnot ⟨r,Subtype.ext hr⟩
    have hfill : ∃ ε : ℝ,0<ε ∧ ball (F q) ε⊆range F:=by
      by_cases hqfront : (F q).1∈frontier P
      · obtain ⟨ε,hε,hfull⟩:=pointTranslatedStrip_removed_boundary_local_fullness
          ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact hcharts q hqfront hqtop
        refine ⟨ε,hε,?_⟩
        intro z hz
        obtain ⟨w,hw⟩:=hfull z.1 z.2 hz.le
        exact ⟨w,Subtype.ext hw⟩
      · have hpint : (F q).1∈interior P:=by
          by_contra hi
          exact hqfront ⟨subset_closure (F q).2,hi⟩
        have hzero:=hcleanInterior (F q).1 hpint ⟨mem_range_self q,hqtop⟩
        obtain ⟨C⟩:=exists_pointInterior_zeroExponent_flatDiskChart ha y hpint hzero
        obtain ⟨r,hr,u,hu,hqu⟩:=q.2
        have hr0 : r≠0:=by
          intro hr0
          have he : q=translatedStripEdge (⟨u,hu⟩ : Icc (0:ℝ) b):=by
            apply Subtype.ext
            change q.1 = flatShearedPoint (conePhase stripAngle) 0 u
            simpa only [hr0] using hqu
          exact hqfront (he.symm ▸ hedge ⟨u,hu⟩)
        have hu0 : u≠0:=by
          intro hu0
          have he : q=translatedStripBottom hb.le (⟨r,hr⟩ : NNReal):=by
            apply Subtype.ext
            change q.1 = flatShearedPoint (conePhase stripAngle) r 0
            simpa only [hu0] using hqu
          exact hqfront (he.symm ▸ hbottom ⟨r,hr⟩)
        have hrpos : 0<r:=lt_of_le_of_ne hr (Ne.symm hr0)
        have hupos : 0<u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hub : u<b:=lt_of_le_of_ne hu.2 (fun he ↦
          hqtop ((translatedStrip_image_mem_top_iff hvi hb.le hFval q hr hqu).mpr he))
        let O : Set ℂ:=(flatShearHomeomorph hvi) '' (Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) b)
        have hOo : IsOpen O:=(flatShearHomeomorph hvi).isOpenMap _ (isOpen_Ioi.prod isOpen_Ioo)
        have hqO : q.1∈O:=⟨(r,u),⟨hrpos,hupos,hub⟩,hqu.symm⟩
        have hOT : O⊆flatShearedStrip (conePhase stripAngle) b:=by
          rintro z ⟨⟨s,v⟩,⟨hs,hv⟩,rfl⟩
          exact ⟨s,hs.le,v,⟨hv.1.le,hv.2.le⟩,rfl⟩
        obtain ⟨η,hη,hηO⟩:=Metric.mem_nhds_iff.mp (hOo.mem_nhds hqO)
        let ε:=min C.radius η
        have hε : 0<ε:=lt_min C.radius_pos hη
        have hεC : ε≤C.radius:=min_le_left _ _
        have hεη : ε≤η:=min_le_right _ _
        refine ⟨ε,hε,metricFlatDisk_isometry_locally_full F hFi q C hε hεC ?_⟩
        intro z hz
        exact hOT (hηO (hz.trans_le hεη))
    obtain ⟨ε,hε,hfill⟩:=hfill
    exact Filter.mem_of_superset
      (Filter.inter_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) (htopclosed.isOpen_compl.mem_nhds hqnot))
      (fun _ hw ↦ ⟨hfill hw.1,hw.2⟩)
  have he : range F \ range (F ∘ translatedStripTop hb.le) =
      {z : P | z.1∈range (fun x ↦ (F x).1) \
        range (fun r ↦ (F (translatedStripTop hb.le r)).1)}:=by
    ext z
    constructor
    · rintro ⟨⟨w,rfl⟩,hw⟩
      refine ⟨mem_range_self w,?_⟩
      rintro ⟨r,hr⟩
      exact hw ⟨r,Subtype.ext hr⟩
    · rintro ⟨⟨w,hw⟩,ht⟩
      refine ⟨⟨w,Subtype.ext hw⟩,?_⟩
      rintro ⟨r,hr⟩
      exact ht ⟨r,congrArg Subtype.val hr⟩
  rw [he] at ho
  change @IsOpen P M.toUniformSpace.toTopologicalSpace _ at ho
  rw [pointRegionMetricSpace_topology ha y P] at ho
  exact ho

end RepulsiveCoulomb
