import LeanResearch.RepulsiveCoulomb.PointTranslatedStripApexFullness

/-! NEW SOURCE-ONLY, UNCOMPILED. Full local image coverage at every removed
old regular edge point. Width pi is derived from an actual halfdisk and its
two actual old-boundary edge germs, without a zero-turn assumption. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointFlatBoundaryPatch_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P U : Set ℂ} (F : U→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    {β L : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi) (hL : 0<L)
    (J : flatLinkSectorDisk β L→U) (hJ : Isometry J) (q : U)
    (hJ0 : J (flatLinkSectorDiskApex hβ.le hL.le)=q)
    (hfront : ∀ r : ℝ, ∀ hr : r∈Icc (0:ℝ) L,
      (F (J (flatLinkSectorDiskPoint hβ.le hβπ r hr 0))).1∈frontier P ∧
      (F (J (flatLinkSectorDiskPoint hβ.le hβπ r hr 1))).1∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (F q).1) (hC : C.Admissible) :
    C.flatPhysicalWidth=β ∧ ∃ ρ : ℝ,0<ρ ∧ ∀ z∈P,
      (pointSmoothConformalEDist a y z (F q).1).toReal≤ρ → z∈range (fun x ↦ (F x).1) := by
  let f : flatLinkSectorDisk β L→ℂ:=fun w ↦ (F (J w)).1
  have hcenter : f (flatLinkSectorDiskApex hβ.le hL.le)=(F q).1:=
    congrArg (fun x ↦ (F x).1) hJ0
  let C0:=C.transportCenter hcenter.symm
  have hC0 : C0.Admissible:=by simpa only [C0, PointRetainedConeNeighborhood.transportCenter_admissible] using hC
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=by rw [hF]; exact hJ.dist_eq x z
  let ρ:=min L (C0.radius/2)
  have hρ : 0<ρ:=lt_min hL (half_pos C0.radius_pos)
  have hρL : ρ≤L:=min_le_left _ _
  have hρC : ρ<C0.radius:=(min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  obtain ⟨hwidth,hfill⟩:=pointFlatLinkDisk_fills_old_boundary_interval ha y hβ hβπ hL
    f hd (fun w ↦ (F (J w)).2) C0 hC0 hρ hρL hρC
    (hfront ρ ⟨hρ.le,hρL⟩).1 (hfront ρ ⟨hρ.le,hρL⟩).2
  refine ⟨by simpa only [C0, PointRetainedConeNeighborhood.transportCenter_width] using hwidth,ρ,hρ,?_⟩
  intro z hzP hz
  have hz0 : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal≤ρ:=by rwa [hcenter]
  obtain ⟨w,hw⟩:=(hfill z hz0).mpr hzP
  exact ⟨J w,hw⟩

theorem pointTranslatedStrip_bottom_width_and_local_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hbottom : ∀ t : NNReal,(F (translatedStripBottom hb.le t)).1∈frontier P)
    (t : NNReal) (ht : 0<t)
    (C : PointRetainedConeNeighborhood a y P (F (translatedStripBottom hb.le t)).1)
    (hC : C.Admissible) :
    C.flatPhysicalWidth=Real.pi ∧ ∃ ρ : ℝ,0<ρ ∧ ∀ z∈P,
      (pointSmoothConformalEDist a y z (F (translatedStripBottom hb.le t)).1).toReal≤ρ →
        z∈range (fun x ↦ (F x).1) := by
  have hs:=Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  let L:=min b (t:ℝ)*Real.sin stripAngle/2
  obtain ⟨hL,hLb,hLt⟩:=translatedStripHorizontal_radius stripAngle_pos stripAngle_lt_pi hb ht
  let J:=translatedStripBottomSource hs hLb hLt
  have hJ0 : J (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=translatedStripBottom hb.le t:=by
    apply Subtype.ext
    change translatedStripBottomRigid t 0=flatShearedPoint (conePhase stripAngle) t 0
    simp only [translatedStripBottomRigid_zero,flatShearedPoint_zero]
  have hfront (r : ℝ) (hr : r∈Icc (0:ℝ) L) :
      (F (J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 0))).1∈frontier P ∧
      (F (J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 1))).1∈frontier P := by
    have hrt : r≤t:=hr.2.trans (hLt.trans (mul_le_of_le_one_right t.2 (Real.sin_le_one stripAngle)))
    let rp : NNReal:=⟨(t:ℝ)+r,add_nonneg t.2 hr.1⟩
    let rm : NNReal:=⟨(t:ℝ)-r,sub_nonneg.mpr hrt⟩
    have he0 : J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 0)=translatedStripBottom hb.le rp:=by
      apply Subtype.ext
      change translatedStripBottomRigid t (sectorPolar r (Real.pi*(0:unitInterval).1))=
        flatShearedPoint (conePhase stripAngle) ((t:ℝ)+r) 0
      simp only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero,
        translatedStripBottomRigid_edge_zero,flatShearedPoint_zero]
    have he1 : J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 1)=translatedStripBottom hb.le rm:=by
      apply Subtype.ext
      change translatedStripBottomRigid t (sectorPolar r (Real.pi*(1:unitInterval).1))=
        flatShearedPoint (conePhase stripAngle) ((t:ℝ)-r) 0
      simp only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one,
        translatedStripBottomRigid_edge_pi,flatShearedPoint_zero]
    exact ⟨he0.symm ▸ hbottom rp,he1.symm ▸ hbottom rm⟩
  exact pointFlatBoundaryPatch_fullness ha y F hF Real.pi_pos le_rfl hL J
    (translatedStripBottomSource_isometry hs hLb hLt) (translatedStripBottom hb.le t) hJ0 hfront C hC

theorem pointTranslatedStrip_edge_width_and_local_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hedge : ∀ u : Icc (0:ℝ) b,(F (translatedStripEdge u)).1∈frontier P)
    (u : Icc (0:ℝ) b) (hu : 0<u.1) (hub : u.1<b)
    (C : PointRetainedConeNeighborhood a y P (F (translatedStripEdge u)).1)
    (hC : C.Admissible) :
    C.flatPhysicalWidth=Real.pi ∧ ∃ ρ : ℝ,0<ρ ∧ ∀ z∈P,
      (pointSmoothConformalEDist a y z (F (translatedStripEdge u)).1).toReal≤ρ →
        z∈range (fun x ↦ (F x).1) := by
  have hs:=Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  let L:=min u.1 (b-u.1)*Real.sin stripAngle/2
  obtain ⟨hL,hLu,hLbu⟩:=translatedStripEdge_radius stripAngle_pos stripAngle_lt_pi hu hub
  let J:=translatedStripEdgeSource hs hLu hLbu
  have hJ0 : J (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=translatedStripEdge u:=by
    apply Subtype.ext
    exact translatedStripCornerRigid_zero stripAngle u.1
  have hfront (r : ℝ) (hr : r∈Icc (0:ℝ) L) :
      (F (J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 0))).1∈frontier P ∧
      (F (J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 1))).1∈frontier P := by
    have hru : r≤u.1:=hr.2.trans (hLu.trans (mul_le_of_le_one_right u.2.1 (Real.sin_le_one stripAngle)))
    have hrbu : r≤b-u.1:=hr.2.trans (hLbu.trans
      (mul_le_of_le_one_right (sub_nonneg.mpr u.2.2) (Real.sin_le_one stripAngle)))
    let um : Icc (0:ℝ) b:=⟨u.1-r,sub_nonneg.mpr hru,(sub_le_self _ hr.1).trans u.2.2⟩
    let up : Icc (0:ℝ) b:=⟨u.1+r,add_nonneg u.2.1 hr.1,by linarith⟩
    have he0 : J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 0)=translatedStripEdge um:=by
      apply Subtype.ext
      change translatedStripCornerRigid stripAngle u.1 (sectorPolar r (Real.pi*(0:unitInterval).1))=
        flatShearedPoint (conePhase stripAngle) 0 (u.1-r)
      simp only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero,
        translatedStripCornerRigid_edge_zero]
    have he1 : J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 1)=translatedStripEdge up:=by
      apply Subtype.ext
      change translatedStripCornerRigid stripAngle u.1 (sectorPolar r (Real.pi*(1:unitInterval).1))=
        flatShearedPoint (conePhase stripAngle) 0 (u.1+r)
      simp only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one,
        translatedStripEdgeRigid_edge_pi]
    exact ⟨he0.symm ▸ hedge um,he1.symm ▸ hedge up⟩
  exact pointFlatBoundaryPatch_fullness ha y F hF Real.pi_pos le_rfl hL J
    (translatedStripEdgeSource_isometry hs hLu hLbu) (translatedStripEdge u) hJ0 hfront C hC

end RepulsiveCoulomb
