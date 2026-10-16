module

public import LeanResearch.RepulsiveCoulomb.RetainedSectorPassingHalfDisk
public import LeanResearch.RepulsiveCoulomb.PointBoundedCornerRetainedChart
public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorRelativeOpenness

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. After constructing the first departure radius r,
this file constructs every field of the new chart at z from an ACTUAL source
halfdisk. The occupied angle pi and outgoing tail germ are derived. A literal
residual identity must first come from global cut topology; it is not proved
here, and no residual chart/angle/coefficient is taken as a certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Upper tail based at the genuine departure radius, rather than at the
original disappearing apex. -/
def disappearingSectorTail {β : ℝ} (hβ : 0≤β) (hβπ : β≤Real.pi)
    (r t : NNReal) : closedEuclideanSector β :=
  retainedApexUpperSource hβ hβπ (r+t)

theorem disappearingSectorTail_isometry {β : ℝ} (hβ : 0≤β) (hβπ : β≤Real.pi)
    (r : NNReal) : Isometry (disappearingSectorTail hβ hβπ r) := by
  apply Isometry.of_dist_eq
  intro s t
  dsimp only [disappearingSectorTail]
  rw [(retainedApexUpperSource_isometry hβ hβπ).dist_eq]
  change |((r:ℝ)+(s:ℝ))-((r:ℝ)+(t:ℝ))|=|(s:ℝ)-(t:ℝ)|
  congr 1
  ring

theorem disappearingSectorPassing_backward {β r L ρ : ℝ}
    (hβ : 0<β) (hβπ : β≤Real.pi)
    (hLsin : β<Real.pi → L≤r*Real.sin β)
    (hρ : 0≤ρ) (hρL : ρ≤L) (hρr : ρ≤r) :
    retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ρ ⟨hρ,hρL⟩ 0)=
      retainedApexUpperSource hβ.le hβπ ⟨r-ρ,sub_nonneg.mpr hρr⟩ := by
  apply Subtype.ext
  change sectorPolar r β-conePhase β*sectorPolar ρ (Real.pi*(0:unitInterval).1)=sectorPolar (r-ρ) β
  simp only [Set.Icc.coe_zero,mul_zero,sectorPolar,conePhase,Complex.ofReal_zero,
    zero_mul,Complex.exp_zero,mul_one,Complex.ofReal_sub]
  ring

theorem disappearingSectorPassing_forward {β r L ρ : ℝ}
    (hβ : 0<β) (hβπ : β≤Real.pi)
    (hLsin : β<Real.pi → L≤r*Real.sin β)
    (hr : 0≤r) (hρ : 0≤ρ) (hρL : ρ≤L) :
    retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ρ ⟨hρ,hρL⟩ 1)=
      retainedApexUpperSource hβ.le hβπ ⟨r+ρ,add_nonneg hr hρ⟩ := by
  have hpi : sectorPolar ρ Real.pi= -(ρ:ℂ):=by
    apply Complex.ext <;> simp [sectorPolar_re,sectorPolar_im]
  apply Subtype.ext
  change sectorPolar r β-conePhase β*sectorPolar ρ (Real.pi*(1:unitInterval).1)=sectorPolar (r+ρ) β
  rw [Set.Icc.coe_one,mul_one,hpi]
  simp only [sectorPolar,Complex.ofReal_add]
  ring

/-- Complete actual retained chart at z; nu(z)<0 itself gives positive
remaining width. Only contact of the preceding old segment is used locally. -/
theorem pointDisappearingApex_construct_departure_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P Q : Set ℂ} (hσP : ∀ x,σ x∈P)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,(t:ℝ)≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (σ (retainedApexUpperSource hβ.le hβπ r)))
    (hC : C.Admissible) {ν : ℂ →₀ ℝ}
    (hνC : ν (σ (retainedApexUpperSource hβ.le hβπ r))=Real.pi-C.flatPhysicalWidth)
    (hνneg : ν (σ (retainedApexUpperSource hβ.le hβπ r))<0)
    (hQ : Q=P\(range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t)))) :
    ∃ E : PointRetainedConeNeighborhood a y Q (σ (retainedApexUpperSource hβ.le hβπ r)),
      E.flatPhysicalWidth=C.flatPhysicalWidth-Real.pi ∧
      Real.pi-E.flatPhysicalWidth=ν (σ (retainedApexUpperSource hβ.le hβπ r))+Real.pi ∧ E.Admissible := by
  obtain ⟨L,hL,hLr,hLsin⟩:=retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let f : flatLinkSectorDisk Real.pi L → ℂ:=σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin
  let τ : NNReal → ℂ:=fun t ↦ σ (disappearingSectorTail hβ.le hβπ r t)
  have hcenter : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=
      σ (retainedApexUpperSource hβ.le hβπ r):=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le))=_
    rw [retainedSectorPassingHalfDisk_apex hβ hβπ hLsin hL.le r.2]
    rfl
  have hold : ∃ C0 : PointRetainedConeNeighborhood a y P
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      C0.Admissible ∧ C0.flatPhysicalWidth=C.flatPhysicalWidth:=by
    rw [hcenter]
    exact ⟨C,hC,rfl⟩
  obtain ⟨C0,hC0,hwidth0⟩:=hold
  have hremain : Real.pi<C0.flatPhysicalWidth:=by rw [hwidth0]; linarith
  have hd (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=by
    dsimp only [f,Function.comp_apply]
    rw [hσ]
    exact (retainedSectorPassingHalfDisk_isometry hβ hβπ hLsin).dist_eq x z
  have hfP (x : flatLinkSectorDisk Real.pi L) : f x∈P:=hσP _
  have hτ (t : NNReal) : (pointSmoothConformalEDist a y (τ t)
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal=t:=by
    rw [hcenter,hσ]
    dsimp only [disappearingSectorTail]
    rw [(retainedApexUpperSource_isometry hβ.le hβπ).dist_eq]
    change |((r:ℝ)+(t:ℝ))-(r:ℝ)|=(t:ℝ)
    rw [add_sub_cancel_left]
    exact abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) from t.2)
  have hedge (t : NNReal) (ht : (t:ℝ)≤L) :
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨t.2,ht⟩ 1)=τ t:=by
    apply congrArg σ
    exact disappearingSectorPassing_forward hβ hβπ hLsin r.2 t.2 ht
  let ρ:=min L (C0.radius/2)
  have hρ : 0<ρ:=lt_min hL (half_pos C0.radius_pos)
  have hρL : ρ≤L:=min_le_left _ _
  have hρC : ρ<C0.radius:=(min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  have hρr : ρ≤r:=hρL.trans hLr.le
  have hfront : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ρ ⟨hρ.le,hρL⟩ 0)∈frontier P:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P
    rw [disappearingSectorPassing_backward hβ hβπ hLsin hρ.le hρL hρr]
    exact hprefix _ (sub_le_self _ hρ.le)
  have hcoverage (z : ℂ)
      (hz : (pointSmoothConformalEDist a y z
        (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal≤ρ) :
      z∈range σ ↔ z∈range f:=by
    rw [hcenter] at hz
    exact pointRetainedSectorPassingHalfDisk_germ y hβ hβπ hLsin r.2 σ hσ (hz.trans hρL)
  have hresult:=pointBoundedCorner_construct_retained_chart ha y Real.pi_pos le_rfl hL
    f hd τ hτ hedge hfP C0 hC0 hremain hρ hρL hρC hfront hcoverage hQ
  obtain ⟨E,_,_,hwidth,hturn,hadm⟩:=hresult
  have hfinal : ∃ E : PointRetainedConeNeighborhood a y Q
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      E.flatPhysicalWidth=C.flatPhysicalWidth-Real.pi ∧
      Real.pi-E.flatPhysicalWidth=ν (σ (retainedApexUpperSource hβ.le hβπ r))+Real.pi ∧
      E.Admissible := by
    refine ⟨E,?_,?_,hadm⟩
    · simpa only [hwidth0] using hwidth
    · rw [hwidth,hwidth0,hνC]
      ring
  exact Eq.mp (congrArg (fun z : ℂ =>
    ∃ E : PointRetainedConeNeighborhood a y Q z,
      E.flatPhysicalWidth=C.flatPhysicalWidth-Real.pi ∧
      Real.pi-E.flatPhysicalWidth=ν (σ (retainedApexUpperSource hβ.le hβπ r))+Real.pi ∧
      E.Admissible) hcenter) hfinal

end RepulsiveCoulomb
