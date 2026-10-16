module

public import LeanResearch.RepulsiveCoulomb.PointRefinedAngularBranchPasting
public import LeanResearch.RepulsiveCoulomb.PointOccupiedBranchBoundary
public import LeanResearch.RepulsiveCoulomb.DirectedSectorDiskRestriction
public import LeanResearch.RepulsiveCoulomb.ContinuousSubtypeExtension

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED, UNSTAGED.

Construct the occupied branch from its actual paired sector coordinates. The
only angular inputs are the scalar endpoint identities output by the finite
angular construction. The orientation is the Boolean occurring in the polar
formula of B.sourcePatch; no independent orientation, branch law, final atlas,
or seam agreement is assumed. Extensions are used only to give total ambient
functions; their asserted continuity stays on the actual subtype domains.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The canonical sector endpoint which becomes the ordered endpoint `top`
under the *original* source orientation. -/
def occupiedBranchEndpointParameter (forward top : Bool) : unitInterval :=
  if forward then (if top then 1 else 0) else (if top then 0 else 1)

theorem occupiedBranchEndpointParameter_boundary (forward top : Bool) :
    occupiedBranchEndpointParameter forward top = 0 ∨
      occupiedBranchEndpointParameter forward top = 1 := by
  cases forward <;> cases top <;> simp [occupiedBranchEndpointParameter]

@[simp] theorem occupiedBranchEndpointParameter_angle (forward top : Bool) (β : ℝ) :
    flatLinkOrientedAngle forward β (occupiedBranchEndpointParameter forward top) =
      if top then β else 0 := by
  cases forward <;> cases top <;>
    simp [occupiedBranchEndpointParameter, flatLinkOrientedAngle]

namespace PointPairedSectorSurgeryCoordinates
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ} {c : ℝ}

/-- The physical forward map, extended only off the literal sector range. -/
def occupiedForward (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (newlo : ℝ) (forward : Bool) : ℂ → ℂ :=
  continuousSubtypeExtension (range S.map)
    (fun z ↦ directedSectorPlacement newlo B.new.angle forward
      (S.localForward ha hc hc1 B.new z)) 0

/-- The physical inverse on the literal target wedge; outside it the chosen
value is the actual common center. -/
def occupiedInverse (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) : ℂ → ℂ :=
  continuousSubtypeExtension (flatLinkOccupiedDisk ε newlo (newlo + B.new.angle))
    (fun z ↦ (S.localInverse ha hc hc1 B.new
      (directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi
        hε hεnew newlo forward z)).1) p

theorem occupiedForward_eq (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (newlo : ℝ) (forward : Bool) {z : ℂ} (hz : z ∈ range S.map) :
    B.occupiedForward ha hc hc1 newlo forward z =
      directedSectorPlacement newlo B.new.angle forward
        (S.localForward ha hc hc1 B.new ⟨z, hz⟩) :=
  continuousSubtypeExtension_eq _ _ _ hz

theorem occupiedInverse_eq (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) {z : ℂ}
    (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) :
    B.occupiedInverse ha hc hc1 hε hεnew newlo forward z =
      (S.localInverse ha hc hc1 B.new
        (directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi
          hε hεnew newlo forward ⟨z, hz⟩)).1 :=
  continuousSubtypeExtension_eq _ _ _ hz

theorem occupiedForward_continuousOn (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (newlo : ℝ) (forward : Bool) :
    ContinuousOn (B.occupiedForward ha hc hc1 newlo forward) (range S.map) :=
  continuousSubtypeExtension_continuousOn _ _ _
    ((directedSectorPlacement newlo B.new.angle forward).continuous.comp
      (S.localForward_continuous ha hc hc1 B.new))

theorem occupiedInverse_continuousOn (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) :
    ContinuousOn (B.occupiedInverse ha hc hc1 hε hεnew newlo forward)
      (flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) :=
  continuousSubtypeExtension_continuousOn _ _ _
    (continuous_subtype_val.comp ((S.localInverse_continuous ha hc hc1 B.new).comp
      (directedSectorDiskRestriction_continuous B.new.angle_pos B.new.angle_le_pi
        hε hεnew newlo forward)))

/-- Both sharp constants are inherited from the actual physical contraction,
with no loss from the ordered Euclidean placement. -/
theorem occupiedForward_dist_bounds (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (newlo : ℝ) (forward : Bool) {z w : ℂ}
    (hz : z ∈ range S.map) (hw : w ∈ range S.map) :
    c * (pointSmoothConformalEDist a y z w).toReal ≤
        dist (B.occupiedForward ha hc hc1 newlo forward z)
          (B.occupiedForward ha hc hc1 newlo forward w) ∧
      dist (B.occupiedForward ha hc hc1 newlo forward z)
          (B.occupiedForward ha hc hc1 newlo forward w) ≤
        (pointSmoothConformalEDist a y z w).toReal := by
  rw [B.occupiedForward_eq ha hc hc1 newlo forward hz,
    B.occupiedForward_eq ha hc hc1 newlo forward hw,
    (directedSectorPlacement newlo B.new.angle forward).dist_eq]
  exact S.localForward_dist_bounds ha hc hc1 B.new ⟨z, hz⟩ ⟨w, hw⟩

/-- The inverse retains precisely the same c/1 metric comparison. -/
theorem occupiedInverse_dist_bounds (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) {z w : ℂ}
    (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle))
    (hw : w ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) :
    c * (pointSmoothConformalEDist a y
        (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z)
        (B.occupiedInverse ha hc hc1 hε hεnew newlo forward w)).toReal ≤ dist z w ∧
      dist z w ≤ (pointSmoothConformalEDist a y
        (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z)
        (B.occupiedInverse ha hc hc1 hε hεnew newlo forward w)).toReal := by
  rw [B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hz,
    B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hw]
  have h := S.localInverse_dist_bounds ha hc hc1 B.new
    (directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi hε hεnew newlo forward ⟨z, hz⟩)
    (directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi hε hεnew newlo forward ⟨w, hw⟩)
  simpa only [Subtype.dist_eq, directedSectorDiskRestriction,
    (directedSectorPlacement newlo B.new.angle forward).symm.dist_eq] using h

theorem occupiedForward_center (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (newlo : ℝ) (forward : Bool) : B.occupiedForward ha hc hc1 newlo forward p = 0 := by
  rw [B.occupiedForward_eq ha hc hc1 newlo forward B.center_mem_range,
    B.forward_center ha hc hc1, directedSectorPlacement_zero]

theorem occupiedInverse_center (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) :
    B.occupiedInverse ha hc hc1 hε hεnew newlo forward 0 = p := by
  have hz : (0 : ℂ) ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle) := by
    refine ⟨0, ⟨le_rfl, hε.le⟩, newlo, ⟨le_rfl, le_add_of_nonneg_right B.new.angle_pos.le⟩, ?_⟩
    simp [sectorPolar]
  rw [B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hz]
  have hw : directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi
      hε hεnew newlo forward ⟨0, hz⟩ =
      flatLinkSectorDiskApex B.new.angle_pos.le B.new.radius_pos.le := by
    apply Subtype.ext
    change (directedSectorPlacement newlo B.new.angle forward).symm 0 = 0
    apply (directedSectorPlacement newlo B.new.angle forward).injective
    rw [(directedSectorPlacement newlo B.new.angle forward).apply_symm_apply,
      directedSectorPlacement_zero]
  rw [hw, B.inverse_center ha hc hc1]

/-- Target membership follows from actual sector membership and the bound on
the forward norm; it is not a supplied branch law. -/
theorem occupiedForward_mem_target (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) {z : ℂ} (hz : z ∈ range S.map)
    (hn : ‖B.occupiedForward ha hc hc1 newlo forward z‖ ≤ ε) :
    B.occupiedForward ha hc hc1 newlo forward z ∈
      flatLinkOccupiedDisk ε newlo (newlo + B.new.angle) := by
  rw [B.occupiedForward_eq ha hc hc1 newlo forward hz,
    directedSectorPlacement_norm] at hn
  apply (directedSectorPlacement_mem_disk_iff B.new.angle_pos B.new.angle_le_pi
    hε newlo forward _).mpr
  rw [B.occupiedForward_eq ha hc hc1 newlo forward hz,
    (directedSectorPlacement newlo B.new.angle forward).symm_apply_apply]
  exact ⟨S.localForward_mem_sector ha hc hc1 B.new ⟨z, hz⟩ (hn.trans hεnew), hn⟩

theorem occupiedInverse_mem_range (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) {z : ℂ}
    (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) :
    B.occupiedInverse ha hc hc1 hε hεnew newlo forward z ∈ range S.map := by
  rw [B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hz]
  exact (S.localInverse ha hc hc1 B.new _).2

theorem occupiedForward_occupiedInverse (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) {z : ℂ}
    (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) :
    B.occupiedForward ha hc hc1 newlo forward
      (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z) = z := by
  let w := directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi
    hε hεnew newlo forward ⟨z, hz⟩
  have hg : B.occupiedInverse ha hc hc1 hε hεnew newlo forward z =
      (S.localInverse ha hc hc1 B.new w).1 :=
    B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hz
  rw [hg, B.occupiedForward_eq ha hc hc1 newlo forward
    (S.localInverse ha hc hc1 B.new w).2]
  change directedSectorPlacement newlo B.new.angle forward
    (S.localForward ha hc hc1 B.new (S.localInverse ha hc hc1 B.new w)) = z
  rw [S.localForward_localInverse ha hc hc1 B.new]
  exact directedSectorDiskRestriction_placed B.new.angle_pos B.new.angle_le_pi
    hε hεnew newlo forward ⟨z, hz⟩

theorem occupiedInverse_occupiedForward (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius)
    (newlo : ℝ) (forward : Bool) {z : ℂ} (hz : z ∈ range S.map)
    (hn : ‖B.occupiedForward ha hc hc1 newlo forward z‖ ≤ ε) :
    B.occupiedInverse ha hc hc1 hε hεnew newlo forward
      (B.occupiedForward ha hc hc1 newlo forward z) = z := by
  have ht := B.occupiedForward_mem_target ha hc hc1 hε hεnew newlo forward hz hn
  have hn' : ‖S.localForward ha hc hc1 B.new ⟨z, hz⟩‖ ≤ B.new.radius := by
    rw [B.occupiedForward_eq ha hc hc1 newlo forward hz,
      directedSectorPlacement_norm] at hn
    exact hn.trans hεnew
  rw [B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward ht]
  have hw : directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi
      hε hεnew newlo forward ⟨B.occupiedForward ha hc hc1 newlo forward z, ht⟩ =
      ⟨S.localForward ha hc hc1 B.new ⟨z, hz⟩,
        S.localForward_mem_sector ha hc hc1 B.new ⟨z, hz⟩ hn', hn'⟩ := by
    apply Subtype.ext
    change (directedSectorPlacement newlo B.new.angle forward).symm
      (B.occupiedForward ha hc hc1 newlo forward z) = _
    rw [B.occupiedForward_eq ha hc hc1 newlo forward hz,
      (directedSectorPlacement newlo B.new.angle forward).symm_apply_apply]
  rw [hw, S.localInverse_localForward ha hc hc1 B.new ⟨z, hz⟩ hn']

/-- The strict small-target bound forces the actual physical inverse into
the old radius. -/
theorem occupiedInverse_small_old_ball (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {R ε : ℝ} (hε : 0 < ε) (hεnew : ε ≤ B.new.radius) (hεcR : ε ≤ c * R)
    (newlo : ℝ) (forward : Bool) {z : ℂ}
    (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) (hn : ‖z‖ < ε) :
    (pointSmoothConformalEDist a y
      (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z) p).toReal < R := by
  rw [B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hz]
  apply B.inverse_small_old_ball ha hc hc1
  rw [directedSectorDiskRestriction_norm]
  exact hn.trans_le hεcR

/-- Actual endpoint formula for the forward map in the rotated common chart.
Chart injectivity identifies the endpoint with its original physical seam. -/
theorem occupiedForward_endpoint (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {R : ℝ} (hRold : R ≤ B.old.radius)
    (hRnew : R ≤ B.new.radius) (hRC : R ≤ C.radius)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin newlo : ℝ) {z : ℂ} (hz : z ∈ pointConeOpenBall (C.rotate (-origin)) R)
    (r : ℝ) (hr : 0 ≤ r) (top : Bool)
    (he : (C.rotate (-origin)).chart z = sectorPolar r
      (normalizedIncidentLower origin lo +
        if top then B.old.angle / (coalescedPointExponent a y p / 2 + 1) else 0)) :
    B.occupiedForward ha hc hc1 newlo forward z =
      sectorPolar r (newlo + if top then B.new.angle else 0) := by
  let D := C.rotate (-origin)
  let t := occupiedBranchEndpointParameter forward top
  have hrR : r ≤ R := by
    have hn : ‖D.chart z‖ < R := by
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hz.2
    rw [he, sectorPolar_norm hr] at hn
    exact hn.le
  let q := flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r
    ⟨hr, hrR.trans hRold⟩ t
  have hqd : (pointSmoothConformalEDist a y (B.sourcePatch.map q) p).toReal = r := by
    have hm := B.sourcePatch.metric q
      (flatLinkSectorDiskApex B.old.angle_pos.le B.old.radius_pos.le)
    rw [B.sourcePatch.map_center] at hm
    refine hm.trans ?_
    change dist (sectorPolar r (B.old.angle * t.1)) 0 = r
    rw [dist_zero_right, sectorPolar_norm hr]
  have hqS : B.sourcePatch.map q ∈ D.chart.source := by
    apply D.source
    change (pointSmoothConformalEDist a y (B.sourcePatch.map q) p).toReal ≤ D.radius
    exact hqd.le.trans (hrR.trans hRC)
  have hqchart : D.chart (B.sourcePatch.map q) = D.chart z := by
    rw [he]
    simpa only [q, t, D, sourcePatch, PointIncidentSectorSourcePatch.map,
      Function.comp_apply, occupiedBranchEndpointParameter_angle] using
      B.sourcePatch.rotated_normalized_polarAt C hpolar origin r ⟨hr, hrR⟩ t
  have hqz : B.sourcePatch.map q = z := D.chart.injOn hqS hz.1 hqchart
  rw [← hqz, B.occupiedForward_eq ha hc hc1 newlo forward
    (show B.sourcePatch.map q ∈ range S.map from mem_range_self _)]
  simpa only [q, t, sourcePatch, PointIncidentSectorSourcePatch.map,
    Function.comp_apply, occupiedBranchEndpointParameter_angle] using
    B.placed_forward_seam ha hc hc1 newlo forward r hr (hrR.trans hRold)
      (hrR.trans hRnew) t (occupiedBranchEndpointParameter_boundary forward top)

/-- Actual inverse endpoint formula: inverse placement recovers the same
canonical endpoint and the paired seam theorem identifies its old chart. -/
theorem occupiedInverse_endpoint (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {R ε : ℝ} (hRold : R ≤ B.old.radius)
    (hε : 0 < ε) (hεR : ε ≤ R) (hεnew : ε ≤ B.new.radius)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin newlo : ℝ) {z : ℂ}
    (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle)) (hn : ‖z‖ < ε)
    (r : ℝ) (hr : 0 ≤ r) (top : Bool)
    (he : z = sectorPolar r (newlo + if top then B.new.angle else 0)) :
    (C.rotate (-origin)).chart (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z) =
      sectorPolar r (normalizedIncidentLower origin lo +
        if top then B.old.angle / (coalescedPointExponent a y p / 2 + 1) else 0) := by
  let t := occupiedBranchEndpointParameter forward top
  have hrε : r ≤ ε := by rw [he, sectorPolar_norm hr] at hn; exact hn.le
  let w := flatLinkSectorDiskPoint B.new.angle_pos.le B.new.angle_le_pi r
    ⟨hr, hrε.trans hεnew⟩ t
  have hw : directedSectorDiskRestriction B.new.angle_pos B.new.angle_le_pi
      hε hεnew newlo forward ⟨z, hz⟩ = w := by
    apply Subtype.ext
    change (directedSectorPlacement newlo B.new.angle forward).symm z =
      sectorPolar r (B.new.angle * t.1)
    apply (directedSectorPlacement newlo B.new.angle forward).injective
    rw [(directedSectorPlacement newlo B.new.angle forward).apply_symm_apply,
      directedSectorPlacement_polar_unitInterval, he]
    simp only [t, occupiedBranchEndpointParameter_angle]
  rw [B.occupiedInverse_eq ha hc hc1 hε hεnew newlo forward hz, hw]
  simpa only [w, t, occupiedBranchEndpointParameter_angle] using
    B.inverse_seam_rotated_chart ha hc hc1 C hRold hpolar origin r
      ⟨hr, hrε.trans hεR⟩ (hrε.trans hεnew) t
      (occupiedBranchEndpointParameter_boundary forward top)

/-- The occupied branch on the actual refined cell. Its four scalar endpoint
identities come from the finite angular builder; all branch and boundary
laws are constructed here from the paired physical coordinates. -/
def occupiedRefinedAngularBranch (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {R ε : ℝ}
    (hR : 0 < R) (hRold : R ≤ B.old.radius) (hRnew : R ≤ B.new.radius)
    (hRC : R ≤ C.radius) (hε : 0 < ε) (hεcR : ε ≤ c * R)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin newlo : ℝ)
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (x : Σ j : Fin N, Fin (Q.count j))
    (holdlo : Q.node x.1 x.2.castSucc = normalizedIncidentLower origin lo)
    (holdhi : Q.node x.1 x.2.succ = normalizedIncidentLower origin lo +
      B.old.angle / (coalescedPointExponent a y p / 2 + 1))
    (hnewlo : refinedIncidentTargetNode Q width x.1 x.2.castSucc = newlo)
    (hnewhi : refinedIncidentTargetNode Q width x.1 x.2.succ = newlo + B.new.angle) :
    PointRefinedAngularBranch (C.rotate (-origin)) R ε Q width x := by
  let D := C.rotate (-origin)
  have hεR : ε ≤ R := hεcR.trans (mul_le_of_le_one_left hR.le hc1)
  have hεnew : ε ≤ B.new.radius := hεR.trans hRnew
  have hRD : R ≤ D.radius := hRC
  have hsource (z : ℂ) (hz : z ∈ pointConeOpenBall D R) :
      z ∈ pointRefinedSourceSet D R Q x ↔ z ∈ range S.map := by
    have hdist := (mem_pointConeOpenBall_iff D hRD z).mp hz
    have hocc := B.sourcePatch.rotated_normalized_range_iff ha C hR hRold hRC
      hpolar origin hdist.le
    simpa only [pointRefinedSourceSet, mem_setOf_eq, holdlo, holdhi, D, sourcePatch] using hocc.symm
  have htarget : pointRefinedTargetSet ε Q width x =
      flatLinkOccupiedDisk ε newlo (newlo + B.new.angle) := by
    simp only [pointRefinedTargetSet, hnewlo, hnewhi]
  have hsource_endpoint (top : Bool) : refinedIncidentSourceEndpoint Q x top =
      normalizedIncidentLower origin lo +
        if top then B.old.angle / (coalescedPointExponent a y p / 2 + 1) else 0 := by
    cases top <;> simp [refinedIncidentSourceEndpoint, holdlo, holdhi]
  have htarget_endpoint (top : Bool) : refinedIncidentTargetEndpoint Q width x top =
      newlo + if top then B.new.angle else 0 := by
    cases top <;> simp [refinedIncidentTargetEndpoint, hnewlo, hnewhi]
  refine {
    forward := B.occupiedForward ha hc hc1 newlo forward
    inverse := B.occupiedInverse ha hc hc1 hε hεnew newlo forward
    forward_continuous := ?_
    inverse_continuous := ?_
    forward_target := ?_
    inverse_source := ?_
    left_inv := ?_
    right_inv := ?_
    forward_center := B.occupiedForward_center ha hc hc1 newlo forward
    inverse_center := B.occupiedInverse_center ha hc hc1 hε hεnew newlo forward
    forward_endpoint := ?_
    inverse_endpoint := ?_
  }
  · exact (B.occupiedForward_continuousOn ha hc hc1 newlo forward).mono
      (fun z hz ↦ (hsource z hz.1).mp hz.2)
  · exact (B.occupiedInverse_continuousOn ha hc hc1 hε hεnew newlo forward).mono
      (fun z hz ↦ htarget ▸ hz.2)
  · intro z hz hn
    rw [htarget]
    apply B.occupiedForward_mem_target ha hc hc1 hε hεnew newlo forward
      ((hsource z hz.1).mp hz.2)
    exact (show ‖B.occupiedForward ha hc hc1 newlo forward z‖ < ε by
      simpa only [mem_ball, dist_zero_right] using hn).le
  · intro z hz
    have hzt : z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle) := htarget ▸ hz.2
    have hzn : ‖z‖ < ε := by simpa only [mem_ball, dist_zero_right] using hz.1
    have hd := B.occupiedInverse_small_old_ball ha hc hc1 hε hεnew hεcR newlo forward hzt hzn
    have hb := (mem_pointConeOpenBall_iff D hRD _).mpr hd
    exact ⟨hb, (hsource _ hb).mpr
      (B.occupiedInverse_mem_range ha hc hc1 hε hεnew newlo forward hzt)⟩
  · intro z hz hn
    apply B.occupiedInverse_occupiedForward ha hc hc1 hε hεnew newlo forward
      ((hsource z hz.1).mp hz.2)
    exact (show ‖B.occupiedForward ha hc hc1 newlo forward z‖ < ε by
      simpa only [mem_ball, dist_zero_right] using hn).le
  · intro z hz
    exact B.occupiedForward_occupiedInverse ha hc hc1 hε hεnew newlo forward (htarget ▸ hz.2)
  · intro z hz r hr top he
    rw [htarget_endpoint]
    apply B.occupiedForward_endpoint ha hc hc1 C hRold hRnew hRC hpolar origin newlo hz.1 r hr top
    simpa only [hsource_endpoint] using he
  · intro z hz r hr top he
    rw [hsource_endpoint]
    apply B.occupiedInverse_endpoint ha hc hc1 C hRold hε hεR hεnew hpolar origin newlo
      (htarget ▸ hz.2) (by simpa only [mem_ball, dist_zero_right] using hz.1) r hr top
    simpa only [htarget_endpoint] using he

/-- Owned cells are never subdivided. Their refined endpoints are therefore
exactly the coarse old endpoints and the cumulative target start plus the
constructed new angle. This wrapper discharges all four refined equalities. -/
def ownedRefinedAngularBranch (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {R ε : ℝ}
    (hR : 0 < R) (hRold : R ≤ B.old.radius) (hRnew : R ≤ B.new.radius)
    (hRC : R ≤ C.radius) (hε : 0 < ε) (hεcR : ε ≤ c * R)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin : ℝ)
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (i : ι) (v : Fin (Q.count (owner i)))
    (holdlo : u (owner i).castSucc = normalizedIncidentLower origin lo)
    (holdhi : u (owner i).succ = normalizedIncidentLower origin lo +
      B.old.angle / (coalescedPointExponent a y p / 2 + 1))
    (hwidth : width (owner i) = B.new.angle) :
    PointRefinedAngularBranch (C.rotate (-origin)) R ε Q width ⟨owner i, v⟩ := by
  classical
  have howned : owner i ∈ range owner := mem_range_self i
  have hcount : Q.count (owner i) = 1 := Q.occupied_whole (owner i) howned
  have hv0 : v.1 = 0 := by have hv := v.2; omega
  have hvfirst : v.castSucc = (0 : Fin (Q.count (owner i) + 1)) := Fin.ext hv0
  have hvlast : v.succ = Fin.last (Q.count (owner i)) := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    omega
  let newlo := linkCumulativeWidth (finiteLinkWidthSequence width) (owner i).1
  have hnewlo : refinedIncidentTargetNode Q width (owner i) v.castSucc = newlo := by
    rw [hvfirst, refinedIncidentTargetNode_first]
  have hnewhi : refinedIncidentTargetNode Q width (owner i) v.succ = newlo + B.new.angle := by
    have hs := refinedIncidentTargetNode_step Q width (owner i) v
    have hw : refinedIncidentTargetWidth Q width (owner i) v = B.new.angle := by
      simp only [refinedIncidentTargetWidth, if_pos howned, hwidth]
    rw [hw, hnewlo] at hs
    linarith
  apply B.occupiedRefinedAngularBranch ha hc hc1 C hR hRold hRnew hRC hε hεcR
    hpolar origin newlo Q width ⟨owner i, v⟩
  · change Q.node (owner i) v.castSucc = _
    rw [hvfirst, Q.first]
    exact holdlo
  · change Q.node (owner i) v.succ = _
    rw [hvlast, Q.last]
    exact holdhi
  · exact hnewlo
  · exact hnewhi

/-- The occupied constructor together with the sharp pairwise estimates on
exactly the source and target sets consumed by finite metric pasting. -/
theorem exists_ownedRefinedAngularBranch (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {R ε : ℝ}
    (hR : 0 < R) (hRold : R ≤ B.old.radius) (hRnew : R ≤ B.new.radius)
    (hRC : R ≤ C.radius) (hε : 0 < ε) (hεcR : ε ≤ c * R)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin : ℝ)
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (i : ι) (v : Fin (Q.count (owner i)))
    (holdlo : u (owner i).castSucc = normalizedIncidentLower origin lo)
    (holdhi : u (owner i).succ = normalizedIncidentLower origin lo +
      B.old.angle / (coalescedPointExponent a y p / 2 + 1))
    (hwidth : width (owner i) = B.new.angle) :
    ∃ F : PointRefinedAngularBranch (C.rotate (-origin)) R ε Q width ⟨owner i, v⟩,
      (∀ z ∈ pointConeOpenBall (C.rotate (-origin)) R ∩
          pointRefinedSourceSet (C.rotate (-origin)) R Q ⟨owner i, v⟩,
        ∀ w ∈ pointConeOpenBall (C.rotate (-origin)) R ∩
          pointRefinedSourceSet (C.rotate (-origin)) R Q ⟨owner i, v⟩,
        c * (pointSmoothConformalEDist a y z w).toReal ≤ dist (F.forward z) (F.forward w) ∧
          dist (F.forward z) (F.forward w) ≤ (pointSmoothConformalEDist a y z w).toReal) ∧
      (∀ z ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width ⟨owner i, v⟩,
        ∀ w ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width ⟨owner i, v⟩,
        c * (pointSmoothConformalEDist a y (F.inverse z) (F.inverse w)).toReal ≤ dist z w ∧
          dist z w ≤ (pointSmoothConformalEDist a y (F.inverse z) (F.inverse w)).toReal) := by
  classical
  let D := C.rotate (-origin)
  let newlo := linkCumulativeWidth (finiteLinkWidthSequence width) (owner i).1
  have hεR : ε ≤ R := hεcR.trans (mul_le_of_le_one_left hR.le hc1)
  have hεnew : ε ≤ B.new.radius := hεR.trans hRnew
  have howned : owner i ∈ range owner := mem_range_self i
  have hcount : Q.count (owner i) = 1 := Q.occupied_whole (owner i) howned
  have hv0 : v.1 = 0 := by have hv := v.2; omega
  have hvfirst : v.castSucc = (0 : Fin (Q.count (owner i) + 1)) := Fin.ext hv0
  have hvlast : v.succ = Fin.last (Q.count (owner i)) := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have hsource {z : ℂ} (hz : z ∈ pointConeOpenBall D R ∩
      pointRefinedSourceSet D R Q ⟨owner i, v⟩) : z ∈ range S.map := by
    have hd := (mem_pointConeOpenBall_iff D (show R ≤ D.radius from hRC) z).mp hz.1
    apply (B.sourcePatch.rotated_normalized_range_iff ha C hR hRold hRC hpolar origin hd.le).mpr
    simpa only [pointRefinedSourceSet, mem_setOf_eq, hvfirst, hvlast, Q.first, Q.last,
      holdlo, holdhi, D, sourcePatch] using hz.2
  have htarget {z : ℂ} (hz : z ∈ pointRefinedTargetSet ε Q width ⟨owner i, v⟩) :
      z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle) := by
    simpa only [pointRefinedTargetSet, refinedIncidentTargetNode, if_pos howned,
      Fin.val_castSucc, Fin.val_succ, hv0, Nat.zero_add, Nat.cast_zero, Nat.cast_one,
      zero_mul, one_mul, add_zero, hwidth] using hz
  let F := B.ownedRefinedAngularBranch ha hc hc1 C hR hRold hRnew hRC hε hεcR
    hpolar origin Q width i v holdlo holdhi hwidth
  refine ⟨F, ?_, ?_⟩
  · intro z hz w hw
    change c * (pointSmoothConformalEDist a y z w).toReal ≤
        dist (B.occupiedForward ha hc hc1 newlo forward z)
          (B.occupiedForward ha hc hc1 newlo forward w) ∧ _
    exact B.occupiedForward_dist_bounds ha hc hc1 newlo forward (hsource hz) (hsource hw)
  · intro z hz w hw
    change c * (pointSmoothConformalEDist a y
      (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z)
      (B.occupiedInverse ha hc hc1 hε hεnew newlo forward w)).toReal ≤ dist z w ∧ _
    exact B.occupiedInverse_dist_bounds ha hc hc1 hε hεnew newlo forward
      (htarget hz.2) (htarget hw.2)

end PointPairedSectorSurgeryCoordinates
end RepulsiveCoulomb
