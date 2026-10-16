import LeanResearch.RepulsiveCoulomb.PointFlatLinkOldIntervalAlignment
import LeanResearch.RepulsiveCoulomb.PointFlatSectorLinkOccupancy
import LeanResearch.RepulsiveCoulomb.PointRetainedApexRestrictChart
import LeanResearch.RepulsiveCoulomb.PointRetainedApexAngularCut

/-!
SOURCE-ONLY, NOT COMPILED. Derive BOTH occupied-sector and free-ray germs in the
OLD actual retained chart from a supplied CLOSED isometric sector. Isometry
excludes hidden distant source components. The only boundary alignment datum is
a positive-radius point on the given bottom ray at the old lower link endpoint.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The actual upper source ray, including its retained apex. -/
def retainedApexUpperSource {β : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (r : NNReal) : closedEuclideanSector β :=
  ⟨sectorPolar r β, by simpa only [Set.Icc.coe_one, mul_one] using
    (flatLink_polar_mem_sector hβ hβπ (NNReal.coe_nonneg r) (1 : unitInterval))⟩

/-- Derive exact old-chart membership for S and its free ray T simultaneously.
No asserted sector occupancy or new chart appears among the inputs. -/
theorem pointRetainedApex_closed_sector_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0))) = sectorPolar ρ C.lo) :
    let p := σ (flatLinkSectorApex hβ.le)
    let k := coalescedPointExponent a y p/2+1
    let cut := C.lo+β/k
    let T := range (fun r : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ r))
    C.lo < cut ∧ cut ≤ C.hi ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ range σ ↔ C.chart z ∈ pointClosedRadialInterval ρ C.lo cut)) ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval ρ cut cut)) := by
  let p := σ (flatLinkSectorApex hβ.le)
  let k := coalescedPointExponent a y p/2+1
  let cut := C.lo+β/k
  let f : flatLinkSectorDisk β L → ℂ := σ ∘ flatLinkSectorDiskInclusion
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z :=
    hσ (flatLinkSectorDiskInclusion x) (flatLinkSectorDiskInclusion z)
  have hfP (x : flatLinkSectorDisk β L) : f x ∈ P := hσP _
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hcut : C.lo < cut := by dsimp [cut]; exact lt_add_of_pos_right _ (div_pos hβ hk)
  obtain ⟨hupper,hocc⟩ := pointFlatLinkDisk_old_lower_occupancy ha y hβ hβπ hL
    f hd hfP C hC hρ hρL hρC hfirst
  obtain ⟨_,hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y hβ hβπ hL
    f hd hfP C hC hρ hρL hρC hfirst
  have htop (r : NNReal) (hr : (r : ℝ) ≤ ρ) :
      C.chart (σ (retainedApexUpperSource hβ.le hβπ r)) = sectorPolar r cut := by
    let s : unitInterval := ⟨(r:ℝ)/ρ,div_nonneg r.2 hρ.le,(div_le_one hρ).mpr hr⟩
    have hrs : ρ*s.1 = r := mul_div_cancel₀ _ hρ.ne'
    have he : flatLinkSectorDiskInclusion
        (flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
          ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ 1) =
        retainedApexUpperSource hβ.le hβπ r := by
      apply Subtype.ext
      change sectorPolar (ρ*s.1) (β*(1:unitInterval).1) = sectorPolar r β
      simp only [hrs,show ((1:unitInterval):ℝ)=1 from rfl,mul_one]
    have hp := hpolar s 1
    change C.chart (σ (flatLinkSectorDiskInclusion _)) = _ at hp
    rw [he,hrs] at hp
    have hbase : f (flatLinkSectorDiskApex hβ.le hL.le) = p := rfl
    simpa only [hbase, show ((1:unitInterval):ℝ)=1 from rfl, mul_one, cut, k] using hp
  refine ⟨hcut,hupper,?_,?_⟩
  · intro z hz
    exact (pointFlatSector_local_range_iff_disk hβ.le hρL σ hσ hz).trans (hocc z hz)
  · intro z hz
    constructor
    · rintro ⟨r,rfl⟩
      have hr : (r : ℝ) ≤ ρ := by
        rw [hσ] at hz
        change dist (sectorPolar r β) (0:ℂ) ≤ ρ at hz
        rw [dist_zero_right, sectorPolar_norm (NNReal.coe_nonneg r)] at hz
        exact hz
      exact ⟨r,⟨r.2,hr⟩,cut,⟨le_rfl,le_rfl⟩,
        (htop r hr).trans (sectorPolar_eq_pointRadialSectorPoint _ _)⟩
    · rintro ⟨r,hr,θ,hθ,he⟩
      have hθcut : θ = cut := le_antisymm hθ.2 hθ.1
      let r' : NNReal := ⟨r,hr.1⟩
      have hsource : (pointSmoothConformalEDist a y
          (σ (retainedApexUpperSource hβ.le hβπ r')) p).toReal ≤ C.radius := by
        rw [hσ]
        change dist (sectorPolar r β) (0:ℂ) ≤ C.radius
        rw [dist_zero_right,sectorPolar_norm hr.1]
        exact hr.2.trans hρC
      refine ⟨r',C.chart.injOn (C.source hsource) (C.source (hz.trans hρC)) ?_⟩
      rw [htop r' hr.2,sectorPolar_eq_pointRadialSectorPoint]
      change pointRadialSectorPoint r cut = C.chart z
      simpa only [hθcut] using he.symm


/-- Construct the complete retained-apex chart from the ACTUAL supplied sector.
The residual set identity must be furnished by the separate Jordan-side proof.
The strict width hypothesis is the actual positive remaining angle, not a
principal-angle estimate. No residual chart or residual turn is an input. -/
theorem pointRetainedApex_construct_actual_apex_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P Q : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0))) = sectorPolar ρ C.lo)
    (hQ : Q = P \ (range σ \
      range (fun r : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ r)))) :
    ∃ E : PointRetainedConeNeighborhood a y Q (σ (flatLinkSectorApex hβ.le)),
      E.chart = C.chart ∧ E.radius = ρ ∧
      E.flatPhysicalWidth = C.flatPhysicalWidth-β ∧
      Real.pi-E.flatPhysicalWidth = (Real.pi-C.flatPhysicalWidth)+β ∧ E.Admissible := by
  let p := σ (flatLinkSectorApex hβ.le)
  let k := coalescedPointExponent a y p/2+1
  let cut := C.lo+β/k
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  obtain ⟨hlc,_,hS,hT⟩ := pointRetainedApex_closed_sector_germs ha y hβ hβπ hL
    σ hσ hσP C hC hρ hρL hρC hfirst
  have hoccupied : k*(cut-C.lo) = β := by
    dsimp [cut]
    rw [add_sub_cancel_left]
    exact mul_div_cancel₀ _ hk.ne'
  have hch : cut < C.hi := by
    have hw : C.flatPhysicalWidth = k*(C.hi-C.lo) := rfl
    rw [hw] at hremain
    nlinarith [hoccupied]
  let D := C.retainedApexRestrict hρ hρC
  have hD : D.Admissible := hC
  have hproper : D.hi-D.lo < 2*Real.pi :=
    D.coordinate_width_lt_full_of_admissible hD
  let E := D.retainedApexCut hlc.le hch hproper hQ hS hT
  have hwidth : E.flatPhysicalWidth = C.flatPhysicalWidth-β := by
    rw [D.retainedApexCut_width hlc.le hch hproper hQ hS hT]
    change C.flatPhysicalWidth-k*(cut-C.lo) = C.flatPhysicalWidth-β
    rw [hoccupied]
  refine ⟨E,rfl,rfl,hwidth,?_,?_⟩
  · rw [hwidth]
    ring
  · exact D.retainedApexCut_admissible hD hlc.le hch hproper hQ hS hT

end RepulsiveCoulomb
