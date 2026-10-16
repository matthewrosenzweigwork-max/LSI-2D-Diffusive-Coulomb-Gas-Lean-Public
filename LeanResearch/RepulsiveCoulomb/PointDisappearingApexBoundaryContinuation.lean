import LeanResearch.RepulsiveCoulomb.PointDisappearingApexFullness
import LeanResearch.RepulsiveCoulomb.PointRetainedEndpointFrontierConverse
import LeanResearch.RepulsiveCoulomb.PointDisappearingApexDepartureChart

/-! SOURCE-ONLY, UNCOMPILED. Genuine forward boundary continuation at full
occupancy. It uses the derived angular trace of the actual isometric disk and
the actual full old chart. No geodesic-extension uniqueness at a negative cone
is asserted. At zero old turn the old retained width is exactly pi. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Equality of actual full width sends the whole second source edge to the
other OLD boundary endpoint. This establishes initial agreement rather than
requiring it as a two-edge boundary certificate. -/
theorem pointFlatLinkDisk_equal_width_outgoing_frontier
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi) (hL : 0<L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z,(pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z)
    {P : Set ℂ} (hfP : ∀ x,f x∈P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    {ρ : ℝ} (hρ : 0<ρ) (hρL : ρ≤L) (hρC : ρ<C.radius)
    (hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)∈frontier P) :
    ∀ s : ℝ,∀ hs : 0<s,∀ hsρ : s≤ρ,
      f (flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs.le,hsρ.trans hρL⟩ 1)∈frontier P := by
  let k:=coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le))/2+1
  have hk : 0 < k := by
    dsimp [k]
    have hnonneg := coalescedPointExponent_nonneg a y (f (flatLinkSectorDiskApex hβ.le hL.le))
    linarith
  have hspan : C.hi-C.lo=β/k:=by
    change k*(C.hi-C.lo)=β at hfull
    apply (eq_div_iff hk.ne').mpr
    simpa only [mul_comm] using hfull
  have hproper:=C.coordinate_width_lt_full_of_admissible hC
  intro s hs hsρ
  let u : unitInterval:=⟨s/ρ,div_nonneg hs.le hρ.le,(div_le_one hρ).mpr hsρ⟩
  have hsu : ρ*u.1=s:=mul_div_cancel₀ _ hρ.ne'
  have hpoint : flatLinkSectorDiskPoint hβ.le hβπ (ρ*u.1)
      ⟨mul_nonneg hρ.le u.2.1,(mul_le_of_le_one_right hρ.le u.2.2).trans hρL⟩ 1=
      flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs.le,hsρ.trans hρL⟩ 1:=by
    apply Subtype.ext
    change sectorPolar (ρ * u.1) (β * (1 : unitInterval).1) =
      sectorPolar s (β * (1 : unitInterval).1)
    rw [hsu]
  have hdist : (pointSmoothConformalEDist a y
      (f (flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs.le,hsρ.trans hρL⟩ 1))
      (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal=s:=by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    exact sectorPolar_norm hs.le _
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hρ hρL hρC hfront with hlo | hhi
  · obtain ⟨_,hpolar⟩:=pointFlatLinkDisk_old_lower_polar ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hlo
    have he:=hpolar u 1
    rw [hpoint,hsu] at he
    have hcut : C.lo+β/k=C.hi:=by linarith
    dsimp only [k] at hcut
    simp only [Set.Icc.coe_one,mul_one,hcut,sectorPolar_eq_pointRadialSectorPoint] at he
    exact C.endpoint_mem_frontier hproper (hdist.trans_lt (hsρ.trans_lt hρC)) hs
      (Or.inr rfl) he
  · obtain ⟨_,hpolar⟩:=pointFlatLinkDisk_old_upper_polar ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hhi
    have he:=hpolar u 1
    rw [hpoint,hsu] at he
    have hcut : C.hi-β/k=C.lo:=by linarith
    dsimp only [k] at hcut
    simp only [Set.Icc.coe_one,mul_one,hcut,sectorPolar_eq_pointRadialSectorPoint] at he
    exact C.endpoint_mem_frontier hproper (hdist.trans_lt (hsρ.trans_lt hρC)) hs
      (Or.inl rfl) he

/-- At any positive initial-contact point with zero old turn, the original
upper ray continues on the old frontier for a definite positive interval.
The prior upper contact and the actual halfdisk construct the initial edge. -/
theorem pointDisappearingApex_zero_turn_continues
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (σ (retainedApexUpperSource hβ.le hβπ r)))
    (hC : C.Admissible) (hzero : C.flatPhysicalWidth=Real.pi) :
    ∃ ε : ℝ,0<ε ∧ ∀ t : NNReal,(t:ℝ)≤ε →
      σ (disappearingSectorTail hβ.le hβπ r t)∈frontier P := by
  obtain ⟨L,hL,hLr,hLsin⟩:=retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let f : flatLinkSectorDisk Real.pi L → ℂ:=σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin
  have hcenter : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=
      σ (retainedApexUpperSource hβ.le hβπ r):=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le))=_
    rw [retainedSectorPassingHalfDisk_apex hβ hβπ hLsin hL.le (NNReal.coe_nonneg r)]
    rfl
  have hold : ∃ C0 : PointRetainedConeNeighborhood a y P
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      C0.Admissible ∧ C0.flatPhysicalWidth=Real.pi:=by
    rw [hcenter]
    exact ⟨C,hC,hzero⟩
  obtain ⟨C0,hC0,hfull⟩:=hold
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
  have hfront : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ 0)∈frontier P:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P
    rw [disappearingSectorPassing_backward hβ hβπ hLsin hε.le hεL hεr]
    exact hprefix _ (sub_le_self _ hε.le)
  have hcontinue:=pointFlatLinkDisk_equal_width_outgoing_frontier ha y Real.pi_pos le_rfl hL
    f hd hfP C0 hC0 hfull hε hεL hεC hfront
  refine ⟨ε,hε,?_⟩
  intro t ht
  by_cases ht0 : t=0
  · subst t
    simpa only [disappearingSectorTail,add_zero] using hprefix r le_rfl
  · have htp : 0<(t:ℝ):=lt_of_le_of_ne t.2 (fun he ↦ ht0 (Subtype.ext he.symm))
    have hout:=hcontinue t htp ht
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P at hout
    rw [disappearingSectorPassing_forward hβ hβπ hLsin (NNReal.coe_nonneg r)
      (NNReal.coe_nonneg t) (ht.trans hεL)] at hout
    exact hout

/-- Initial upper-boundary agreement is derived from full angle and the
single given bottom frontier, including the apex. -/
theorem pointDisappearingApex_initial_boundary_contact
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ r : NNReal,σ (retainedApexBottomSource hβ.le hβπ r)∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β) :
    ∃ ρ : ℝ,0<ρ ∧ ∀ r : NNReal,(r:ℝ)≤ρ →
      σ (retainedApexUpperSource hβ.le hβπ r)∈frontier P := by
  let ρ:=min 1 C.radius/2
  have hρ : 0<ρ:=half_pos (lt_min (by norm_num) C.radius_pos)
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    linarith [min_le_left (1 : ℝ) C.radius, lt_min (show (0 : ℝ) < 1 by norm_num) C.radius_pos]
  have hρC : ρ < C.radius := by
    dsimp [ρ]
    linarith [min_le_right (1 : ℝ) C.radius, lt_min (show (0 : ℝ) < 1 by norm_num) C.radius_pos]
  let f : flatLinkSectorDisk β 1 → ℂ:=σ ∘ flatLinkSectorDiskInclusion
  have hf : ∀ x z,(pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=
    fun x z ↦ hσ _ _
  have hfP : ∀ x,f x∈P:=fun x ↦ hσP _
  have hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρ1⟩ 0)∈frontier P:=by
    have he : flatLinkSectorDiskInclusion
        (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρ1⟩ 0)=
        retainedApexBottomSource hβ.le hβπ ⟨ρ,hρ.le⟩:=by
      apply Subtype.ext
      change sectorPolar ρ (β * (0 : unitInterval).1) = sectorPolar ρ 0
      simp only [Set.Icc.coe_zero, mul_zero]
    change σ (flatLinkSectorDiskInclusion _)∈frontier P
    rw [he]
    exact hbottom _
  have hout:=pointFlatLinkDisk_equal_width_outgoing_frontier ha y hβ hβπ (by norm_num)
    f hf hfP C hC hfull hρ hρ1 hρC hfront
  refine ⟨ρ,hρ,?_⟩
  intro r hr
  by_cases hr0 : r=0
  · subst r
    have he : retainedApexUpperSource hβ.le hβπ 0=retainedApexBottomSource hβ.le hβπ 0:=by
      apply Subtype.ext
      exact (sectorPolar_zero β).trans (sectorPolar_zero 0).symm
    rw [he]
    exact hbottom 0
  · have hrpos : 0<(r:ℝ):=lt_of_le_of_ne r.2 (fun he ↦ hr0 (Subtype.ext he.symm))
    have he : flatLinkSectorDiskInclusion
        (flatLinkSectorDiskPoint hβ.le hβπ r ⟨r.2,hr.trans hρ1⟩ 1)=
        retainedApexUpperSource hβ.le hβπ r:=by
      apply Subtype.ext
      simp only [flatLinkSectorDiskInclusion,flatLinkSectorDiskPoint,
        retainedApexUpperSource,Set.Icc.coe_one,mul_one]
    have ho:=hout r hrpos hr
    change σ (flatLinkSectorDiskInclusion _)∈frontier P at ho
    rwa [he] at ho

end RepulsiveCoulomb
