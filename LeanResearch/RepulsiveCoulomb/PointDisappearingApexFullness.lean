import LeanResearch.RepulsiveCoulomb.PointFlatLinkBoundaryFullness
import LeanResearch.RepulsiveCoulomb.PointRetainedApexInitialEntry

/-! SOURCE-ONLY, UNCOMPILED. Equality of the supplied sector width with the
actual full old angle implies LITERAL local filling, using only ONE old-boundary
source edge. The other edge is not assumed to be old boundary. This is the
full-angle bridge needed before constructing any first-departure endpoint. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

private theorem disappearingApex_radial_restrict {r R lo hi : ℝ} (hrR : r ≤ R)
    {w : ℂ} (hw : ‖w‖ ≤ r) :
    w ∈ pointClosedRadialInterval R lo hi ↔ w ∈ pointClosedRadialInterval r lo hi := by
  constructor
  · rintro ⟨s,hs,θ,hθ,he⟩
    refine ⟨s,⟨hs.1,?_⟩,θ,hθ,he⟩
    rwa [he,pointRadialSectorPoint_norm hs.1] at hw
  · rintro ⟨s,hs,θ,hθ,he⟩
    exact ⟨s,⟨hs.1,hs.2.trans hrR⟩,θ,hθ,he⟩

/-- Full old interval occupancy from the actual isometric disk, a single
boundary edge point, and equality with the actual old physical width. Both
endpoint orientations are derived and handled; beta=pi is allowed. -/
theorem pointFlatLinkDisk_fills_equal_old_interval
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi) (hL : 0<L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z,(pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z)
    {P : Set ℂ} (hfP : ∀ x,f x∈P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    {ρ : ℝ} (hρ : 0<ρ) (hρL : ρ≤L) (hρC : ρ<C.radius)
    (hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)∈frontier P) :
    ∀ z,(pointSmoothConformalEDist a y z
      (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal≤ρ → (z∈range f ↔ z∈P) := by
  let p:=f (flatLinkSectorDiskApex hβ.le hL.le)
  let k:=coalescedPointExponent a y p/2+1
  have hk : 0<k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hspan : C.hi-C.lo=β/k := by
    change k*(C.hi-C.lo)=β at hfull
    apply (eq_div_iff hk.ne').mpr
    simpa only [mul_comm] using hfull
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hρ hρL hρC hfront with hlo | hhi
  · obtain ⟨_,hocc⟩:=pointFlatLinkDisk_old_lower_occupancy ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hlo
    have he : C.lo+β/k=C.hi := by linarith
    intro z hz
    have hn : ‖C.chart z‖≤ρ :=
      (C.retainedWidth_chart_norm (hz.trans hρC.le)).trans_le hz
    have ho:=hocc z hz
    rw [he] at ho
    exact ho.trans ((disappearingApex_radial_restrict hρC.le hn).symm.trans
      (C.retained z (hz.trans hρC.le)).symm)
  · obtain ⟨_,hocc⟩:=pointFlatLinkDisk_old_upper_occupancy ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hhi
    have he : C.hi-β/k=C.lo := by linarith
    intro z hz
    have hn : ‖C.chart z‖≤ρ :=
      (C.retainedWidth_chart_norm (hz.trans hρC.le)).trans_le hz
    have ho:=hocc z hz
    rw [he] at ho
    exact ho.trans ((disappearingApex_radial_restrict hρC.le hn).symm.trans
      (C.retained z (hz.trans hρC.le)).symm)

/-- The ACTUAL full-angle closed sector fills P near its original apex.
The source restriction covers all distant source candidates by the genuine
all-pairs isometry. No contact with the second boundary end is an input. -/
theorem pointDisappearingApex_sector_locally_full
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ r : NNReal,σ (retainedApexBottomSource hβ.le hβπ r)∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β) :
    ∃ ρ : ℝ,0<ρ ∧ ∀ z,(pointSmoothConformalEDist a y z
      (σ (flatLinkSectorApex hβ.le))).toReal≤ρ → (z∈range σ ↔ z∈P) := by
  let ρ:=min 1 C.radius/2
  have hρ : 0<ρ:=half_pos (lt_min (by norm_num) C.radius_pos)
  have hρ1 : ρ≤1:=
    (half_lt_self (lt_min (show (0:ℝ)<1 by norm_num) C.radius_pos)).le.trans
      (min_le_left _ _)
  have hρC : ρ<C.radius:=
    (half_lt_self (lt_min (show (0:ℝ)<1 by norm_num) C.radius_pos)).trans_le
      (min_le_right _ _)
  let f : flatLinkSectorDisk β 1 → ℂ:=σ ∘ flatLinkSectorDiskInclusion
  have hf : ∀ x z,(pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=
    fun x z ↦ hσ _ _
  have hfP : ∀ x,f x∈P:=fun x ↦ hσP _
  have hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρ1⟩ 0)∈frontier P:=by
    have he : flatLinkSectorDiskInclusion
        (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρ1⟩ 0)=
        retainedApexBottomSource hβ.le hβπ ⟨ρ,hρ.le⟩:=by
      apply Subtype.ext
      simp only [flatLinkSectorDiskInclusion,flatLinkSectorDiskPoint,
        retainedApexBottomSource,Set.Icc.coe_zero,mul_zero]
      rfl
    change σ (flatLinkSectorDiskInclusion _)∈frontier P
    rw [he]
    exact hbottom _
  have hfill:=pointFlatLinkDisk_fills_equal_old_interval ha y hβ hβπ (by norm_num)
    f hf hfP C hC hfull hρ hρ1 hρC hfront
  refine ⟨ρ,hρ,?_⟩
  intro z hz
  exact (pointFlatSector_local_range_iff_disk hβ.le hρ1 σ hσ hz).trans (hfill z hz)

/-- A filled genuine old-metric neighborhood excludes its center from the
LITERAL closed residual. This does not assert a residual topology theorem. -/
theorem point_locally_filled_not_mem_closed_residual
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P S : Set ℂ} {p : ℂ} {ρ : ℝ} (hρ : 0<ρ)
    (hfill : ∀ z,(pointSmoothConformalEDist a y z p).toReal≤ρ → z∈P → z∈S) :
    p∉closure (P\S) := by
  have hn : @Not (p∈@closure ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace (P\S)):=by
    letI : MetricSpace ℂ:=pointSmoothConformalMetricSpace ha y
    intro hp
    obtain ⟨z,hz,hd⟩:=(@Metric.mem_closure_iff ℂ
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace (P\S) p).mp hp ρ hρ
    change (pointSmoothConformalEDist a y p z).toReal < ρ at hd
    rw [pointSmoothConformalEDist_comm a y p z] at hd
    exact hz.2 (hfill z hd.le hz.1)
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hn

/-- The original apex really disappears before any global residual-side
identification; this follows directly from its constructed local fullness. -/
theorem pointDisappearingApex_apex_not_mem_closed_residual
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ r : NNReal,σ (retainedApexBottomSource hβ.le hβπ r)∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β) :
    σ (flatLinkSectorApex hβ.le)∉closure (P\range σ) := by
  obtain ⟨ρ,hρ,hfill⟩:=pointDisappearingApex_sector_locally_full ha y hβ hβπ σ hσ
    hσP hbottom C hC hfull
  exact point_locally_filled_not_mem_closed_residual ha y hρ
    (fun z hz hzP ↦ (hfill z hz).mpr hzP)

end RepulsiveCoulomb
