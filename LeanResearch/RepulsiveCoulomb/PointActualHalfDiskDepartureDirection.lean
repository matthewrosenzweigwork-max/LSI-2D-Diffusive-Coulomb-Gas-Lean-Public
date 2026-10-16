import LeanResearch.RepulsiveCoulomb.PointBoundedCornerRetainedChart
import LeanResearch.RepulsiveCoulomb.PointSectorReturnGermWidthIdentification

/-! SOURCE-ONLY, UNCOMPILED. Produce the ACTUAL raw initial direction and
proper-old-end local germ required by the cap frontend from an actual isometric
halfdisk anchored at the incoming old boundary. The desired pi offset is a
conclusion, not an angle certificate. Only local source-edge formulas are used;
the incoming old end is allowed to bend outside this source disk. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointActualHalfDisk_construct_departure_direction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {L : ℝ} (hL : 0<L) (f : flatLinkSectorDisk Real.pi L → ℂ)
    (hd : ∀ x z,(pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z)
    {P : Set ℂ} (hfP : ∀ x,f x∈P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)))
    (hC : C.Admissible) (hremain : Real.pi<C.flatPhysicalWidth)
    (upper lower : ℝ → ℂ)
    (hedge0 : ∀ s : ℝ,∀ (hs : 0 ≤ s) (hsL : s ≤ L),
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl s ⟨hs,hsL⟩ 0)=lower s)
    (hedge1 : ∀ s : ℝ,∀ (hs : 0 ≤ s) (hsL : s ≤ L),
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl s ⟨hs,hsL⟩ 1)=upper s)
    (E : PointGeodesicTreeEdge a y)
    (hE0 : E.start=f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))
    (hEP : ∀ t,E.curve t∈P)
    (hEcurve : ∀ t : unitInterval,E.curve t=upper (pointActualEdgeLength E*t.1))
    {ρ : ℝ} (hρ : 0<ρ) (hρL : ρ≤L) (hρC : ρ<C.radius)
    (hfront : lower ρ∈frontier P) :
    ∃ ξ : ℝ,ξ∈Icc C.lo C.hi ∧ (ξ=C.lo ∨ ξ=C.hi) ∧
      (C.actualInitialRawAngle ha y hC E hE0 hEP∈Ioo C.lo C.hi) ∧
      (1+coalescedPointExponent a y (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))/2)*
        |C.actualInitialRawAngle ha y hC E hE0 hEP-ξ|=Real.pi ∧
      ∀ t∈Ioo (0:ℝ) ρ,lower t∈C.chart.source ∧
        C.chart (lower t)=pointRadialSectorPoint t ξ := by
  let p:=f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)
  let k:=coalescedPointExponent a y p/2+1
  have hk : 0<k:=by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hfirst : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ρ ⟨hρ.le,hρL⟩ 0)∈frontier P:=by
    rw [hedge0 ρ hρ.le hρL]
    exact hfront
  have hgerm_of (A : unitInterval → ℝ)
      (hpolar : ∀ s t : unitInterval,C.chart (f
        (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl (ρ*s.1)
          ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t))=
        sectorPolar (ρ*s.1) (A t)) :
      (∀ u∈Ioo (0:ℝ) ρ,C.chart (lower u)=pointRadialSectorPoint u (A 0)) ∧
      (∀ u∈Ioo (0:ℝ) ρ,C.chart (upper u)=pointRadialSectorPoint u (A 1)):=by
    have hg (t : unitInterval) (u : ℝ) (hu : u∈Ioo (0:ℝ) ρ) :
        C.chart (f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl u
          ⟨hu.1.le,hu.2.le.trans hρL⟩ t))=pointRadialSectorPoint u (A t):=by
      let s : unitInterval:=⟨u/ρ,div_nonneg hu.1.le hρ.le,(div_le_one hρ).mpr hu.2.le⟩
      have hus : ρ*s.1=u:=mul_div_cancel₀ _ hρ.ne'
      have he:=hpolar s t
      have hp : flatLinkSectorDiskPoint Real.pi_pos.le le_rfl (ρ*s.1)
          ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t=
          flatLinkSectorDiskPoint Real.pi_pos.le le_rfl u ⟨hu.1.le,hu.2.le.trans hρL⟩ t:=by
        apply Subtype.ext
        change sectorPolar (ρ*s.1) (Real.pi*t.1) = sectorPolar u (Real.pi*t.1)
        rw [hus]
      rw [hp,hus,sectorPolar_eq_pointRadialSectorPoint] at he
      exact he
    constructor
    · intro u hu
      have he:=hg 0 u hu
      rwa [hedge0 u hu.1.le (hu.2.le.trans hρL)] at he
    · intro u hu
      have he:=hg 1 u hu
      rwa [hedge1 u hu.1.le (hu.2.le.trans hρL)] at he
  have hlowerSource (u : ℝ) (hu : u∈Ioo (0:ℝ) ρ) : lower u∈C.chart.source:=by
    apply C.source
    change (pointSmoothConformalEDist a y (lower u)
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le))).toReal ≤ C.radius
    rw [← hedge0 u hu.1.le (hu.2.le.trans hρL),pointFlatLinkDiskMap_dist_apex y Real.pi_pos hL f hd]
    change ‖sectorPolar u (Real.pi*(0:unitInterval).1)‖≤C.radius
    rw [sectorPolar_norm hu.1.le]
    exact hu.2.le.trans hρC.le
  rcases pointFlatLinkDisk_first_edge_endpoint Real.pi_pos le_rfl hL f hd hfP C
      hρ hρL hρC hfirst with hlo | hhi
  · obtain ⟨hcutHi,hpolar⟩:=pointFlatLinkDisk_old_lower_polar ha y Real.pi_pos le_rfl hL
      f hd hfP C hC hρ hρL hρC.le hlo
    obtain ⟨hlower,hupper⟩:=hgerm_of (fun t ↦ C.lo+(Real.pi/k)*t.1) hpolar
    have hlow : C.lo∈Icc C.lo C.hi:=⟨le_rfl,C.width_pos.le⟩
    have hcutLo : C.lo<C.lo+Real.pi/k:=lt_add_of_pos_right _ (div_pos Real.pi_pos hk)
    have hcut : C.lo+Real.pi/k<C.hi:=by
      change Real.pi<k*(C.hi-C.lo) at hremain
      have hmul : k*(Real.pi/k)=Real.pi:=mul_div_cancel₀ _ hk.ne'
      nlinarith
    have hlower' : ∀ u∈Ioo (0:ℝ) ρ,C.chart (lower u)=pointRadialSectorPoint u C.lo:=by
      simpa only [Set.Icc.coe_zero,mul_zero,add_zero] using hlower
    have hupper' : ∀ u∈Ioo (0:ℝ) ρ,C.chart (upper u)=pointRadialSectorPoint u (C.lo+Real.pi/k):=by
      simpa only [Set.Icc.coe_one,mul_one] using hupper
    have hraw:=C.reference_angle_eq_actual_clean_germ ha y hC E hE0 hEP upper hEcurve
      hρ ⟨hcutLo.le,hcut.le⟩ hupper'
    refine ⟨C.lo,hlow,Or.inl rfl,hraw.symm ▸ And.intro hcutLo hcut,?_,?_⟩
    · rw [hraw,add_sub_cancel_left,abs_of_pos (div_pos Real.pi_pos hk)]
      simpa only [k,p,add_comm] using (mul_div_cancel₀ Real.pi hk.ne')
    · exact fun u hu ↦ ⟨hlowerSource u hu,hlower' u hu⟩
  · obtain ⟨hcutLo,hpolar⟩:=pointFlatLinkDisk_old_upper_polar ha y Real.pi_pos le_rfl hL
      f hd hfP C hC hρ hρL hρC.le hhi
    obtain ⟨hlower,hupper⟩:=hgerm_of (fun t ↦ C.hi-(Real.pi/k)*t.1) hpolar
    have hhigh : C.hi∈Icc C.lo C.hi:=⟨C.width_pos.le,le_rfl⟩
    have hcutHi : C.hi-Real.pi/k<C.hi:=sub_lt_self _ (div_pos Real.pi_pos hk)
    have hcut : C.lo<C.hi-Real.pi/k:=by
      change Real.pi<k*(C.hi-C.lo) at hremain
      have hmul : k*(Real.pi/k)=Real.pi:=mul_div_cancel₀ _ hk.ne'
      nlinarith
    have hlower' : ∀ u∈Ioo (0:ℝ) ρ,C.chart (lower u)=pointRadialSectorPoint u C.hi:=by
      simpa only [Set.Icc.coe_zero,mul_zero,sub_zero] using hlower
    have hupper' : ∀ u∈Ioo (0:ℝ) ρ,C.chart (upper u)=pointRadialSectorPoint u (C.hi-Real.pi/k):=by
      simpa only [Set.Icc.coe_one,mul_one] using hupper
    have hraw:=C.reference_angle_eq_actual_clean_germ ha y hC E hE0 hEP upper hEcurve
      hρ ⟨hcut.le,hcutHi.le⟩ hupper'
    refine ⟨C.hi,hhigh,Or.inr rfl,hraw.symm ▸ And.intro hcut hcutHi,?_,?_⟩
    · rw [hraw,show C.hi-Real.pi/k-C.hi= -(Real.pi/k) by ring,abs_neg,
        abs_of_pos (div_pos Real.pi_pos hk)]
      simpa only [k,p,add_comm] using (mul_div_cancel₀ Real.pi hk.ne')
    · exact fun u hu ↦ ⟨hlowerSource u hu,hlower' u hu⟩

end RepulsiveCoulomb
