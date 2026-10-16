module

public import LeanResearch.RepulsiveCoulomb.PointFlatLinkFrontierEndpoint
public import LeanResearch.RepulsiveCoulomb.PointRetainedApexRestrictChart
public import LeanResearch.RepulsiveCoulomb.PointRetainedApexAngularCut
public import LeanResearch.RepulsiveCoulomb.PointRetainedUpperApexAngularCut

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. A bounded genuine corner disk and its actual
extended free ray suffice for the new retained chart. The local strip-patch
coverage is supplied by the separate explicit Euclidean source construction.
The literal set identity is supplied by the actual global cut-topology proof.
No residual chart or angle/curvature-update certificate is an input. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Isometry of the actual extended ray excludes hidden distant ray points.
The radial formula here is an intermediate conclusion of the actual corner
isometry, not a datum about the residual. -/
theorem pointCorner_free_ray_germ
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (τ : NNReal → ℂ)
    (hτ : ∀ r, (pointSmoothConformalEDist a y (τ r) p).toReal = r)
    {ρ cut : ℝ} (hρC : ρ ≤ C.radius)
    (hpolar : ∀ r : NNReal, (r : ℝ) ≤ ρ → C.chart (τ r) = sectorPolar r cut) :
    ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
      (z ∈ range τ ↔ C.chart z ∈ pointClosedRadialInterval ρ cut cut) := by
  intro z hz
  constructor
  · rintro ⟨r,rfl⟩
    have hr : (r : ℝ) ≤ ρ := by rwa [hτ] at hz
    exact ⟨r,⟨r.2,hr⟩,cut,⟨le_rfl,le_rfl⟩,
      (hpolar r hr).trans (sectorPolar_eq_pointRadialSectorPoint _ _)⟩
  · rintro ⟨r,hr,θ,hθ,he⟩
    have hθcut : θ = cut := le_antisymm hθ.2 hθ.1
    let r' : NNReal := ⟨r,hr.1⟩
    have hb : (pointSmoothConformalEDist a y (τ r') p).toReal ≤ C.radius := by
      rw [hτ]
      exact hr.2.trans hρC
    refine ⟨r',C.chart.injOn (C.source hb) (C.source (hz.trans hρC)) ?_⟩
    rw [hpolar r' hr.2,sectorPolar_eq_pointRadialSectorPoint]
    change pointRadialSectorPoint r cut = C.chart z
    rw [hθcut] at he
    exact he.symm

/-- An actual source upper edge in a bounded corner patch induces the radial
formula of its whole free ray wherever that ray lies in the patch radius. -/
theorem pointCorner_edge_polar_from_disk
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ) (τ : NNReal → ℂ)
    (hedge : ∀ r : NNReal, ∀ hr : (r : ℝ) ≤ L,
      f (flatLinkSectorDiskPoint hβ.le hβπ r ⟨r.2,hr⟩ 1) = τ r)
    {P : Set ℂ}
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (A : unitInterval → ℝ)
    (hpolar : ∀ s t : unitInterval,
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
        ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
          sectorPolar (ρ*s.1) (A t)) :
    ∀ r : NNReal, (r : ℝ) ≤ ρ → C.chart (τ r) = sectorPolar r (A 1) := by
  intro r hr
  let s : unitInterval := ⟨(r:ℝ)/ρ,div_nonneg r.2 hρ.le,(div_le_one hρ).mpr hr⟩
  have hrs : ρ*s.1 = r := mul_div_cancel₀ _ hρ.ne'
  have he := hpolar s 1
  have hpoint : flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
      ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ 1 =
      flatLinkSectorDiskPoint hβ.le hβπ r ⟨r.2,hr.trans hρL⟩ 1 := by
    apply Subtype.ext
    change sectorPolar (ρ*s.1) (β*((1 : unitInterval) : ℝ)) =
      sectorPolar r (β*((1 : unitInterval) : ℝ))
    rw [hrs]
  rw [hpoint,hedge r (hr.trans hρL),hrs] at he
  exact he

/-- Full retained chart from the bounded ACTUAL corner and old frontier.
Both endpoint orientations are considered explicitly. Every field of E is
constructed by literal radial subtraction in the actual old chart. -/
theorem pointBoundedCorner_construct_retained_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (τ : NNReal → ℂ)
    (hτ : ∀ r, (pointSmoothConformalEDist a y (τ r)
      (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal = r)
    (hedge : ∀ r : NNReal, ∀ hr : (r : ℝ) ≤ L,
      f (flatLinkSectorDiskPoint hβ.le hβπ r ⟨r.2,hr⟩ 1) = τ r)
    {P Q S : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ < C.radius)
    (hfront : f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0) ∈ frontier P)
    (hcoverage : ∀ z, (pointSmoothConformalEDist a y z
        (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal ≤ ρ →
      (z ∈ S ↔ z ∈ range f))
    (hQ : Q = P \ (S \ range τ)) :
    ∃ E : PointRetainedConeNeighborhood a y Q (f (flatLinkSectorDiskApex hβ.le hL.le)),
      E.chart = C.chart ∧ E.radius = ρ ∧
      E.flatPhysicalWidth = C.flatPhysicalWidth-β ∧
      Real.pi-E.flatPhysicalWidth = (Real.pi-C.flatPhysicalWidth)+β ∧ E.Admissible := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p/2+1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  let D := C.retainedApexRestrict hρ hρC.le
  have hD : D.Admissible := hC
  have hproper : D.hi-D.lo < 2*Real.pi :=
    D.coordinate_width_lt_full_of_admissible hD
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hρ hρL hρC hfront with hlo | hhi
  · let cut := C.lo+β/k
    obtain ⟨_,hocc⟩ := pointFlatLinkDisk_old_lower_occupancy ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hlo
    obtain ⟨_,hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hlo
    have htop : ∀ r : NNReal, (r : ℝ) ≤ ρ → C.chart (τ r) = sectorPolar r cut := by
      have ht := pointCorner_edge_polar_from_disk hβ hβπ hL f τ hedge C hρ hρL
        (fun t ↦ C.lo+(β/k)*t.1) hpolar
      simpa only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one] using ht
    have hT := pointCorner_free_ray_germ C τ hτ hρC.le htop
    have hS (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ ρ) :
        z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval ρ C.lo cut :=
      (hcoverage z hz).trans (hocc z hz)
    have hoccupied : k*(cut-C.lo) = β := by
      dsimp [cut]
      rw [add_sub_cancel_left]
      exact mul_div_cancel₀ _ hk.ne'
    have hlc : C.lo ≤ cut := by dsimp [cut]; linarith [div_pos hβ hk]
    have hch : cut < C.hi := by
      change β < k*(C.hi-C.lo) at hremain
      nlinarith [hoccupied]
    let E := D.retainedApexCut hlc hch hproper hQ hS hT
    have hw : E.flatPhysicalWidth = C.flatPhysicalWidth-β := by
      rw [D.retainedApexCut_width hlc hch hproper hQ hS hT]
      change C.flatPhysicalWidth-k*(cut-C.lo) = C.flatPhysicalWidth-β
      rw [hoccupied]
    refine ⟨E,rfl,rfl,hw,?_,D.retainedApexCut_admissible hD hlc hch hproper hQ hS hT⟩
    rw [hw]
    ring
  · let cut := C.hi-β/k
    obtain ⟨_,hocc⟩ := pointFlatLinkDisk_old_upper_occupancy ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hhi
    obtain ⟨_,hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y hβ hβπ hL
      f hd hfP C hC hρ hρL hρC.le hhi
    have htop : ∀ r : NNReal, (r : ℝ) ≤ ρ → C.chart (τ r) = sectorPolar r cut := by
      have ht := pointCorner_edge_polar_from_disk hβ hβπ hL f τ hedge C hρ hρL
        (fun t ↦ C.hi-(β/k)*t.1) hpolar
      simpa only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one] using ht
    have hT := pointCorner_free_ray_germ C τ hτ hρC.le htop
    have hS (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ ρ) :
        z ∈ S ↔ C.chart z ∈ pointClosedRadialInterval ρ cut C.hi :=
      (hcoverage z hz).trans (hocc z hz)
    have hoccupied : k*(C.hi-cut) = β := by
      dsimp [cut]
      rw [sub_sub_cancel]
      exact mul_div_cancel₀ _ hk.ne'
    have hlc : C.lo < cut := by
      change β < k*(C.hi-C.lo) at hremain
      nlinarith [hoccupied]
    have hch : cut ≤ C.hi := by dsimp [cut]; linarith [div_pos hβ hk]
    let E := D.retainedUpperApexCut hlc hch hproper hQ hS hT
    have hw : E.flatPhysicalWidth = C.flatPhysicalWidth-β := by
      rw [D.retainedUpperApexCut_width hlc hch hproper hQ hS hT]
      change C.flatPhysicalWidth-k*(C.hi-cut) = C.flatPhysicalWidth-β
      rw [hoccupied]
    refine ⟨E,rfl,rfl,hw,?_,D.retainedUpperApexCut_admissible hD hlc hch hproper hQ hS hT⟩
    rw [hw]
    ring

end RepulsiveCoulomb
