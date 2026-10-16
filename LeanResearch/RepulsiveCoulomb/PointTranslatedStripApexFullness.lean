module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripLocalSources
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripCornerChart
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkBoundaryFullness

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Actual local filling at the removed apex p.
The old physical angle lambda and its positive turn pi-lambda are DERIVED from
the supplied translated strip and exact old-boundary contact. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_apex_width_and_local_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b → P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (C : PointRetainedConeNeighborhood a y P (F (translatedStripBottom hb.le 0)).1)
    (hC : C.Admissible) :
    C.flatPhysicalWidth=stripAngle ∧
      Real.pi-C.flatPhysicalWidth=Real.pi-stripAngle ∧
      ∃ ρ : ℝ,0<ρ ∧ ∀ z∈P,
        (pointSmoothConformalEDist a y z (F (translatedStripBottom hb.le 0)).1).toReal≤ρ →
          z∈range (fun x ↦ (F x).1) := by
  let L:=b*Real.sin stripAngle/2
  obtain ⟨hL,hLbound⟩:=translatedStripCorner_radius stripAngle_pos stripAngle_lt_pi hb
  let J:=translatedStripBottomCornerSource stripAngle_pos stripAngle_lt_pi hLbound
  let f : flatLinkSectorDisk stripAngle L → ℂ:=fun w ↦ (F (J w)).1
  have hJ0 : J (flatLinkSectorDiskApex stripAngle_pos.le hL.le)=translatedStripBottom hb.le 0 := by
    apply Subtype.ext
    simp [J,translatedStripBottomCornerSource,flatLinkSectorDiskApex,
      translatedStripBottom,flatShearedPoint]
  have hcenter : f (flatLinkSectorDiskApex stripAngle_pos.le hL.le)=
      (F (translatedStripBottom hb.le 0)).1 := congrArg (fun x ↦ (F x).1) hJ0
  let C0:=C.transportCenter hcenter.symm
  have hC0 : C0.Admissible := by
    simpa only [C0, PointRetainedConeNeighborhood.transportCenter_admissible] using hC
  have hd (x z : flatLinkSectorDisk stripAngle L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z := by
    rw [hF]
    exact (translatedStripBottomCornerSource_isometry stripAngle_pos stripAngle_lt_pi hLbound).dist_eq x z
  have hfP (x : flatLinkSectorDisk stripAngle L) : f x∈P := (F (J x)).2
  let ρ:=min L (C0.radius/2)
  have hρ : 0<ρ:=lt_min hL (half_pos C0.radius_pos)
  have hρL : ρ≤L:=min_le_left _ _
  have hρC : ρ<C0.radius:=(min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  have hρb : ρ≤b:=hρL.trans (hLbound.trans
    (mul_le_of_le_one_right hb.le (Real.sin_le_one stripAngle)))
  let r : NNReal:=⟨ρ,hρ.le⟩
  let u : Icc (0:ℝ) b:=⟨ρ,hρ.le,hρb⟩
  have hfirst : J (flatLinkSectorDiskPoint stripAngle_pos.le stripAngle_lt_pi.le ρ ⟨hρ.le,hρL⟩ 0)=
      translatedStripBottom hb.le r := by
    apply Subtype.ext
    change sectorPolar ρ (stripAngle*(0:unitInterval).1)=flatShearedPoint (conePhase stripAngle) ρ 0
    simp only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero,
      translatedStrip_sectorPolar_zero_angle,flatShearedPoint_zero]
  have hlast : J (flatLinkSectorDiskPoint stripAngle_pos.le stripAngle_lt_pi.le ρ ⟨hρ.le,hρL⟩ 1)=
      translatedStripEdge u := by
    apply Subtype.ext
    change sectorPolar ρ (stripAngle*(1:unitInterval).1)=flatShearedPoint (conePhase stripAngle) 0 ρ
    simp only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one,
      translatedStripBottomCorner_edge_aperture]
  have hfront0 : f (flatLinkSectorDiskPoint stripAngle_pos.le stripAngle_lt_pi.le ρ ⟨hρ.le,hρL⟩ 0)∈frontier P := by
    change (F (J _)).1∈frontier P
    rw [hfirst]
    have hm : (F (translatedStripBottom hb.le r)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inl ⟨r,rfl⟩
    exact hm.2
  have hfront1 : f (flatLinkSectorDiskPoint stripAngle_pos.le stripAngle_lt_pi.le ρ ⟨hρ.le,hρL⟩ 1)∈frontier P := by
    change (F (J _)).1∈frontier P
    rw [hlast]
    have hm : (F (translatedStripEdge u)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inr ⟨u,rfl⟩
    exact hm.2
  obtain ⟨hwidth,hfill⟩:=pointFlatLinkDisk_fills_old_boundary_interval ha y stripAngle_pos stripAngle_lt_pi.le hL
    f hd hfP C0 hC0 hρ hρL hρC hfront0 hfront1
  have hw : C.flatPhysicalWidth=stripAngle := by
    simpa only [C0, PointRetainedConeNeighborhood.transportCenter_width] using hwidth
  refine ⟨hw,by rw [hw],ρ,hρ,?_⟩
  intro z hzP hz
  have hz0 : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex stripAngle_pos.le hL.le))).toReal≤ρ := by
    rwa [hcenter]
  obtain ⟨w,hw⟩:=(hfill z hz0).mpr hzP
  exact ⟨J w,hw⟩

end RepulsiveCoulomb
