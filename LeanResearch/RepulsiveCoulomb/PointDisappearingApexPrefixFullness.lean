module

public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexWholeContact

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Every point strictly inside the original common
upper-boundary segment has actual full retained width pi and no curvature turn.
The local halfdisk radius is constructed to stay within that genuine prefix. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointDisappearingApex_upper_prefix_full
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (R : ℝ) (hupper : ∀ t : NNReal,(t:ℝ)≤R →
      σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (r : NNReal) (hr : 0<(r:ℝ)) (hrR : (r:ℝ)<R)
    (C : PointRetainedConeNeighborhood a y P (σ (retainedApexUpperSource hβ.le hβπ r)))
    (hC : C.Admissible) :
    C.flatPhysicalWidth=Real.pi ∧ ∃ ε : ℝ,0<ε ∧ ∀ z,
      (pointSmoothConformalEDist a y z (σ (retainedApexUpperSource hβ.le hβπ r))).toReal≤ε →
        (z∈range σ ↔ z∈P) := by
  obtain ⟨L0,hL0,hL0r,hL0sin⟩:=retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let L:=min L0 ((R-(r:ℝ))/2)
  have hL : 0<L:=lt_min hL0 (half_pos (sub_pos.mpr hrR))
  have hLL0 : L≤L0:=min_le_left _ _
  have hLr : L<(r:ℝ):=hLL0.trans_lt hL0r
  have hLsin : β<Real.pi → L≤(r:ℝ)*Real.sin β:=fun h ↦ hLL0.trans (hL0sin h)
  have hLR : (r:ℝ)+L≤R:=by
    have := min_le_right L0 ((R-(r:ℝ))/2)
    change L≤(R-(r:ℝ))/2 at this
    linarith
  let f : flatLinkSectorDisk Real.pi L → ℂ:=σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin
  have hcenter : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=
      σ (retainedApexUpperSource hβ.le hβπ r):=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le))=_
    rw [retainedSectorPassingHalfDisk_apex hβ hβπ hLsin hL.le (NNReal.coe_nonneg r)]
    rfl
  have hold : ∃ C0 : PointRetainedConeNeighborhood a y P
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      C0.Admissible ∧ C0.flatPhysicalWidth=C.flatPhysicalWidth:=by
    rw [hcenter]
    exact ⟨C,hC,rfl⟩
  obtain ⟨C0,hC0,hwidth0⟩:=hold
  have hd (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=by
    dsimp only [f, Function.comp_apply]
    rw [hσ]
    exact (retainedSectorPassingHalfDisk_isometry hβ hβπ hLsin).dist_eq x z
  have hfP (x : flatLinkSectorDisk Real.pi L) : f x∈P:=hσP _
  let ε:=min L (C0.radius/2)
  have hε : 0<ε:=lt_min hL (half_pos C0.radius_pos)
  have hεL : ε≤L:=min_le_left _ _
  have hεC : ε<C0.radius:=(min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  have hεr : ε≤r:=hεL.trans hLr.le
  have hfront0 : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ 0)∈frontier P:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P
    rw [disappearingSectorPassing_backward hβ hβπ hLsin hε.le hεL hεr]
    exact hupper _ (by change (r:ℝ)-ε≤R; linarith)
  have hfront1 : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ 1)∈frontier P:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P
    rw [disappearingSectorPassing_forward hβ hβπ hLsin r.2 hε.le hεL]
    exact hupper _ (by change (r:ℝ)+ε≤R; linarith)
  obtain ⟨hwidth,hfill⟩:=pointFlatLinkDisk_fills_old_boundary_interval ha y Real.pi_pos le_rfl hL
    f hd hfP C0 hC0 hε hεL hεC hfront0 hfront1
  rw [hcenter] at hfill
  refine ⟨hwidth0.symm.trans hwidth,ε,hε,?_⟩
  intro z hz
  exact (pointRetainedSectorPassingHalfDisk_germ y hβ hβπ hLsin r.2 σ hσ
    (hz.trans hεL)).trans (hfill z hz)

end RepulsiveCoulomb
