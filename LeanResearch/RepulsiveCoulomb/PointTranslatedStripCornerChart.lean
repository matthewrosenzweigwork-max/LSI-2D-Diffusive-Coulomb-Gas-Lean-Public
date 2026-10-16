import LeanResearch.RepulsiveCoulomb.TranslatedStripCornerSourceV2
import LeanResearch.RepulsiveCoulomb.PointBoundedCornerRetainedChart

/-! NEW SOURCE-ONLY, UNCOMPILED. Concrete target chart at z=F(b*v), obtained
from the supplied literal translated strip. Corner coverage, free-ray germ,
old-endpoint placement, full retained interval and exact turn are constructed.
The global literal removed-set identity must first be PROVED by the cut-topology
construction; no residual chart/homeomorphism/update is assumed here. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

namespace PointRetainedConeNeighborhood

def transportCenter {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p q : ℂ} (C : PointRetainedConeNeighborhood a y P p) (h : p=q) :
    PointRetainedConeNeighborhood a y P q := h ▸ C

@[simp] theorem transportCenter_chart {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p q : ℂ} (C : PointRetainedConeNeighborhood a y P p) (h : p=q) :
    (C.transportCenter h).chart=C.chart := by cases h; rfl

@[simp] theorem transportCenter_width {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p q : ℂ} (C : PointRetainedConeNeighborhood a y P p) (h : p=q) :
    (C.transportCenter h).flatPhysicalWidth=C.flatPhysicalWidth := by cases h; rfl

@[simp] theorem transportCenter_admissible {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p q : ℂ} (C : PointRetainedConeNeighborhood a y P p) (h : p=q) :
    (C.transportCenter h).Admissible ↔ C.Admissible := by cases h; rfl

end PointRetainedConeNeighborhood

/-- The concrete translated corner, with both old-boundary orientations
allowed, has retained physical width lambda_P(z)-(pi-lambda). This is the full
retained chart construction, not a principal-angle or scalar-only assertion. -/
theorem pointTranslatedStrip_construct_corner_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b → P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (C : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb.le 0)).1)
    (hC : C.Admissible) (hremain : Real.pi-stripAngle<C.flatPhysicalWidth)
    (hQ : Q=P \ (range (fun x ↦ (F x).1) \
      range (fun r ↦ (F (translatedStripTop hb.le r)).1))) :
    ∃ E : PointRetainedConeNeighborhood a y Q (F (translatedStripTop hb.le 0)).1,
      E.chart=C.chart ∧ E.flatPhysicalWidth=C.flatPhysicalWidth-(Real.pi-stripAngle) ∧
      Real.pi-E.flatPhysicalWidth=(Real.pi-C.flatPhysicalWidth)+(Real.pi-stripAngle) ∧ E.Admissible := by
  let β := Real.pi-stripAngle
  let L := b*Real.sin stripAngle/2
  have hβ : 0<β := sub_pos.mpr stripAngle_lt_pi
  have hβπ : β≤Real.pi := by dsimp [β]; linarith
  obtain ⟨hL,hLbound⟩ := translatedStripCorner_radius stripAngle_pos stripAngle_lt_pi hb
  let J := translatedStripCornerSource stripAngle_pos stripAngle_lt_pi hLbound
  let f : flatLinkSectorDisk β L → ℂ := fun x ↦ (F (J x)).1
  let τ : NNReal → ℂ := fun r ↦ (F (translatedStripTop hb.le r)).1
  have hJ0 : J (flatLinkSectorDiskApex hβ.le hL.le)=translatedStripTop hb.le 0 := by
    apply Subtype.ext
    change translatedStripCornerRigid stripAngle b 0=flatShearedPoint (conePhase stripAngle) 0 b
    exact translatedStripCornerRigid_zero stripAngle b
  have hcenter : f (flatLinkSectorDiskApex hβ.le hL.le)=τ 0 :=
    congrArg (fun x ↦ (F x).1) hJ0
  let C0 := C.transportCenter hcenter.symm
  have hC0 : C0.Admissible := by
    simpa only [C0, PointRetainedConeNeighborhood.transportCenter_admissible] using hC
  have hremain0 : β<C0.flatPhysicalWidth := by
    simpa only [C0, β, PointRetainedConeNeighborhood.transportCenter_width] using hremain
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z := by
    rw [hF]
    exact (translatedStripCornerSource_isometry stripAngle_pos stripAngle_lt_pi hLbound).dist_eq x z
  have hfP (x : flatLinkSectorDisk β L) : f x∈P := (F (J x)).2
  have hτ (r : NNReal) :
      (pointSmoothConformalEDist a y (τ r) (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal=r := by
    rw [hcenter,hF,(translatedStripTop_isometry hb.le).dist_eq]
    simp only [NNReal.dist_eq,NNReal.coe_zero,sub_zero]
    exact abs_of_nonneg r.2
  have hedge (r : NNReal) (hr : (r:ℝ)≤L) :
      f (flatLinkSectorDiskPoint hβ.le hβπ r ⟨r.2,hr⟩ 1)=τ r := by
    apply congrArg (fun x ↦ (F x).1)
    apply Subtype.ext
    change translatedStripCornerRigid stripAngle b (sectorPolar r (β*(1:unitInterval).1)) =
      flatShearedPoint (conePhase stripAngle) r b
    simp only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one]
    exact translatedStripCornerRigid_edge_aperture stripAngle b r
  let ρ := min L (C0.radius/2)
  have hρ : 0<ρ := lt_min hL (half_pos C0.radius_pos)
  have hρL : ρ≤L := min_le_left _ _
  have hρC : ρ<C0.radius := (min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  have hρb : ρ≤b := hρL.trans (hLbound.trans
    (mul_le_of_le_one_right hb.le (Real.sin_le_one stripAngle)))
  let u : Icc (0:ℝ) b := ⟨b-ρ,sub_nonneg.mpr hρb,sub_le_self _ hρ.le⟩
  have hfirstsource : J (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)=
      translatedStripEdge u := by
    apply Subtype.ext
    change translatedStripCornerRigid stripAngle b (sectorPolar ρ (β*(0:unitInterval).1)) =
      flatShearedPoint (conePhase stripAngle) 0 (b-ρ)
    simp only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero]
    exact translatedStripCornerRigid_edge_zero stripAngle b ρ
  have hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)∈frontier P := by
    change (F (J _)).1∈frontier P
    rw [hfirstsource]
    have hm : (F (translatedStripEdge u)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inr ⟨u,rfl⟩
    exact hm.2
  have hcoverage (z : ℂ)
      (hz : (pointSmoothConformalEDist a y z (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal≤ρ) :
      z∈range (fun x ↦ (F x).1) ↔ z∈range f := by
    constructor
    · rintro ⟨q,rfl⟩
      rw [hcenter,hF] at hz
      obtain ⟨w,hw⟩ := translatedStripCornerSource_local_coverage stripAngle_pos stripAngle_lt_pi hb.le hLbound q
        (hz.trans hρL)
      exact ⟨w,congrArg (fun x ↦ (F x).1) hw⟩
    · rintro ⟨w,rfl⟩
      exact ⟨J w,rfl⟩
  obtain ⟨E,hchart,hradius,hwidth,hturn,hadm⟩ :=
    pointBoundedCorner_construct_retained_chart ha y hβ hβπ hL f hd τ hτ hedge hfP
      C0 hC0 hremain0 hρ hρL hρC hfront hcoverage hQ
  refine ⟨E.transportCenter hcenter,?_,?_,?_,?_⟩
  · simpa only [C0, PointRetainedConeNeighborhood.transportCenter_chart] using hchart
  · simpa only [C0, β, PointRetainedConeNeighborhood.transportCenter_width] using hwidth
  · simpa only [C0, β, PointRetainedConeNeighborhood.transportCenter_width] using hturn
  · simpa only [PointRetainedConeNeighborhood.transportCenter_admissible] using hadm

end RepulsiveCoulomb
