module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripLocalSources
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripCornerChart
public import LeanResearch.RepulsiveCoulomb.PointActualHalfDiskComplement

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Every positive-time point of the actual free
top ray gets a genuine FULL complementary retained chart. The input may be an
old interior cone atom. Its old coefficient -pi*a is preserved exactly. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_construct_open_top_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b → P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (hQ : Q=P \ (range (fun x ↦ (F x).1) \
      range (fun r ↦ (F (translatedStripTop hb.le r)).1)))
    (r : NNReal) (hr : 0<r) :
    (F (translatedStripTop hb.le r)).1∈interior P ∧
    ∃ E : PointRetainedConeNeighborhood a y Q (F (translatedStripTop hb.le r)).1,
      E.flatPhysicalWidth=
        (coalescedPointExponent a y (F (translatedStripTop hb.le r)).1/2+1)*(2*Real.pi)-Real.pi ∧
      Real.pi-E.flatPhysicalWidth=
        -Real.pi*coalescedPointExponent a y (F (translatedStripTop hb.le r)).1 ∧ E.Admissible := by
  have hs : 0<Real.sin stripAngle := Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  have hvi : (conePhase stripAngle).im≠0 := by rw [conePhase_im]; exact hs.ne'
  obtain ⟨hclosed,hproper⟩ := pointTranslatedStrip_closed_proper ha y hvi F hF
  have hpint := pointTranslatedStrip_open_top_interior hvi hb F hclosed.injective hcontact r hr
  let p := (F (translatedStripTop hb.le r)).1
  have hnhds : interior P∈@nhds ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact isOpen_interior.mem_nhds hpint
  obtain ⟨η,hη,hηsub⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hnhds
  obtain ⟨hB,hBb,hBr⟩ := translatedStripHorizontal_radius stripAngle_pos stripAngle_lt_pi hb hr
  let B := min b (r:ℝ)*Real.sin stripAngle/2
  let L := min B (η/2)
  have hL : 0<L := lt_min hB (half_pos hη)
  have hLB : L≤B := min_le_left _ _
  have hLb : L≤b*Real.sin stripAngle := hLB.trans hBb
  have hLr : L≤(r:ℝ)*Real.sin stripAngle := hLB.trans hBr
  have hLη : L<η := (min_le_right _ _).trans_lt (half_lt_self hη)
  let J := translatedStripTopSource hs hLb hLr
  let f : flatLinkSectorDisk Real.pi L → ℂ := fun x ↦ (F (J x)).1
  have hJ0 : J (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=translatedStripTop hb.le r := by
    apply Subtype.ext
    change translatedStripTopRigid stripAngle b r 0=flatShearedPoint (conePhase stripAngle) r b
    exact translatedStripTopRigid_zero stripAngle b r
  have hcenter : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=p :=
    congrArg (fun x ↦ (F x).1) hJ0
  have hd (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z := by
    rw [hF]
    exact (translatedStripTopSource_isometry hs hLb hLr).dist_eq x z
  have hPball (z : ℂ)
      (hz : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤L) : z∈P := by
    apply interior_subset
    apply hηsub
    change (pointSmoothConformalEDist a y z p).toReal<η
    rw [hcenter] at hz
    exact hz.trans_lt hLη
  have hS (z : ℂ)
      (hz : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤L) :
      z∈range (fun x ↦ (F x).1) ↔ z∈range f := by
    constructor
    · rintro ⟨q,rfl⟩
      rw [hcenter,hF] at hz
      obtain ⟨w,hw⟩ := translatedStripTopSource_local_coverage hs hLb hLr q hz
      exact ⟨w,congrArg (fun x ↦ (F x).1) hw⟩
    · rintro ⟨w,rfl⟩
      exact ⟨J w,rfl⟩
  have hT (z : ℂ)
      (hz : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤L) :
      z∈range (fun t ↦ (F (translatedStripTop hb.le t)).1) ↔ z∈f '' {w | w.1.im=0} := by
    constructor
    · rintro ⟨t,rfl⟩
      obtain ⟨w,hw⟩ := (hS _ hz).mp ⟨translatedStripTop hb.le t,rfl⟩
      have hsrc : J w∈range (translatedStripTop hb.le) :=
        ⟨t,(hclosed.injective hw).symm⟩
      have him : w.1.im=0 :=
        (translatedStripTopSource_mem_top_iff hs hb.le hLb hLr w).mp hsrc
      exact ⟨w,him,hw⟩
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨t,ht⟩ := (translatedStripTopSource_mem_top_iff hs hb.le hLb hLr w).mpr hw
      exact ⟨t,congrArg (fun x ↦ (F x).1) ht⟩
  obtain ⟨E,hwidth,hatom,hadm⟩ := pointActualHalfDisk_construct_complementary_chart
    ha y hL f hd hPball hS hT hQ
  refine ⟨hpint,E.transportCenter hcenter,?_,?_,?_⟩
  · simpa only [PointRetainedConeNeighborhood.transportCenter_width,hcenter] using hwidth
  · simpa only [PointRetainedConeNeighborhood.transportCenter_width,hcenter] using hatom
  · simpa only [PointRetainedConeNeighborhood.transportCenter_admissible] using hadm

end RepulsiveCoulomb
