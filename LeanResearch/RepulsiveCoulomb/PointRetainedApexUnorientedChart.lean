module

public import LeanResearch.RepulsiveCoulomb.PointRetainedApexSectorGerms
public import LeanResearch.RepulsiveCoulomb.PointRetainedUpperApexAngularCut
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkFrontierEndpoint

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. Both old endpoint orientations are derived from
actual source-bottom membership in the old frontier. No lower-endpoint premise,
reflected chart, or principal-angle orientation is silently imposed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointRetainedApex_closed_sector_upper_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0))) = sectorPolar ρ C.hi) :
    let p := σ (flatLinkSectorApex hβ.le)
    let k := coalescedPointExponent a y p/2+1
    let cut := C.hi-β/k
    let T := range (fun r : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ r))
    C.lo ≤ cut ∧ cut < C.hi ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ range σ ↔ C.chart z ∈ pointClosedRadialInterval ρ cut C.hi)) ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ T ↔ C.chart z ∈ pointClosedRadialInterval ρ cut cut)) := by
  let p := σ (flatLinkSectorApex hβ.le)
  let k := coalescedPointExponent a y p/2+1
  let cut := C.hi-β/k
  let f : flatLinkSectorDisk β L → ℂ := σ ∘ flatLinkSectorDiskInclusion
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z :=
    hσ (flatLinkSectorDiskInclusion x) (flatLinkSectorDiskInclusion z)
  have hfP (x : flatLinkSectorDisk β L) : f x ∈ P := hσP _
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hcut : cut < C.hi := by dsimp [cut]; exact sub_lt_self _ (div_pos hβ hk)
  obtain ⟨hupper,hocc⟩ := pointFlatLinkDisk_old_upper_occupancy ha y hβ hβπ hL
    f hd hfP C hC hρ hρL hρC hfirst
  obtain ⟨_,hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y hβ hβπ hL
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
  refine ⟨hupper,hcut,?_,?_⟩
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


/-- Complete chart construction in the upper old-endpoint case. -/
theorem pointRetainedApex_construct_actual_upper_apex_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P Q : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0))) = sectorPolar ρ C.hi)
    (hQ : Q = P \ (range σ \
      range (fun r : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ r)))) :
    ∃ E : PointRetainedConeNeighborhood a y Q (σ (flatLinkSectorApex hβ.le)),
      E.chart = C.chart ∧ E.radius = ρ ∧
      E.flatPhysicalWidth = C.flatPhysicalWidth-β ∧
      Real.pi-E.flatPhysicalWidth = (Real.pi-C.flatPhysicalWidth)+β ∧ E.Admissible := by
  let p := σ (flatLinkSectorApex hβ.le)
  let k := coalescedPointExponent a y p/2+1
  let cut := C.hi-β/k
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  obtain ⟨_,hch,hS,hT⟩ := pointRetainedApex_closed_sector_upper_germs ha y hβ hβπ hL
    σ hσ hσP C hC hρ hρL hρC hfirst
  have hoccupied : k*(C.hi-cut) = β := by
    dsimp [cut]
    rw [sub_sub_cancel]
    exact mul_div_cancel₀ _ hk.ne'
  have hlc : C.lo < cut := by
    have hw : C.flatPhysicalWidth = k*(C.hi-C.lo) := rfl
    rw [hw] at hremain
    nlinarith [hoccupied]
  let D := C.retainedApexRestrict hρ hρC
  have hD : D.Admissible := hC
  have hproper : D.hi-D.lo < 2*Real.pi :=
    D.coordinate_width_lt_full_of_admissible hD
  let E := D.retainedUpperApexCut hlc hch.le hproper hQ hS hT
  have hwidth : E.flatPhysicalWidth = C.flatPhysicalWidth-β := by
    rw [D.retainedUpperApexCut_width hlc hch.le hproper hQ hS hT]
    change C.flatPhysicalWidth-k*(C.hi-cut) = C.flatPhysicalWidth-β
    rw [hoccupied]
  refine ⟨E,rfl,rfl,hwidth,?_,?_⟩
  · rw [hwidth]
    ring
  · exact D.retainedUpperApexCut_admissible hD hlc hch.le hproper hQ hS hT

/-- The orientation-free supplied-sector apex endpoint. The clean bottom edge
is only required to lie in the ACTUAL old boundary at the chosen positive
radius; old-chart endpoint placement is then proved. Literal Q identification
remains the separate global Jordan-cut obligation, not assumed chart data. -/
theorem pointRetainedApex_construct_apex_chart_from_frontier
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P Q : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ < C.radius)
    (hfront : σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) ∈ frontier P)
    (hQ : Q = P \ (range σ \
      range (fun r : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ r)))) :
    ∃ E : PointRetainedConeNeighborhood a y Q (σ (flatLinkSectorApex hβ.le)),
      E.chart = C.chart ∧ E.radius = ρ ∧
      E.flatPhysicalWidth = C.flatPhysicalWidth-β ∧
      Real.pi-E.flatPhysicalWidth = (Real.pi-C.flatPhysicalWidth)+β ∧ E.Admissible := by
  let f : flatLinkSectorDisk β L → ℂ := σ ∘ flatLinkSectorDiskInclusion
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z :=
    hσ (flatLinkSectorDiskInclusion x) (flatLinkSectorDiskInclusion z)
  have hfP (x : flatLinkSectorDisk β L) : f x ∈ P := hσP _
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hρ hρL hρC hfront with hlo | hhi
  · exact pointRetainedApex_construct_actual_apex_chart ha y hβ hβπ hL
      σ hσ hσP C hC hremain hρ hρL hρC.le hlo hQ
  · exact pointRetainedApex_construct_actual_upper_apex_chart ha y hβ hβπ hL
      σ hσ hσP C hC hremain hρ hρL hρC.le hhi hQ

end RepulsiveCoulomb
