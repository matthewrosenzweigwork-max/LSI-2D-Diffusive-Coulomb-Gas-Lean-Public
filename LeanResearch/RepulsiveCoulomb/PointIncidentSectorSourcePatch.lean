import LeanResearch.RepulsiveCoulomb.PointFlatLinkOpenArcLifting
import LeanResearch.RepulsiveCoulomb.CenteredHalfDiskInteriorTransfer
import LeanResearch.RepulsiveCoulomb.PointActualSectorIncidentOccupancy

/-! SOURCE-ONLY, UNCOMPILED. Retain the constructed actual source patch,
rather than forgetting it after proving occupancy. It is built from a
literal sector boundary point, and supplies the interior-image fact needed
for disjoint open arcs and an actual seam-origin choice. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

structure PointIncidentSectorSourcePatch
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) (p : ℂ) where
  angle : ℝ
  angle_pos : 0 < angle
  angle_le_pi : angle ≤ Real.pi
  radius : ℝ
  radius_pos : 0 < radius
  sourceMap : flatLinkSectorDisk angle radius → closedEuclideanSector S.beta
  isometry : Isometry sourceMap
  center : S.map (sourceMap (flatLinkSectorDiskApex angle_pos.le radius_pos.le)) = p
  local_range : ∀ q : closedEuclideanSector S.beta,
    dist q (sourceMap (flatLinkSectorDiskApex angle_pos.le radius_pos.le)) ≤ radius →
      q ∈ range sourceMap
  interior : ∀ x : flatLinkSectorDisk angle radius,
    x.1 ∈ interior (closedEuclideanSector angle) → 0 < x.1.im → ‖x.1‖ < radius →
      (sourceMap x).1 ∈ interior (closedEuclideanSector S.beta)
  angle_eq : angle = if p = S.apex then S.beta else Real.pi

namespace PointIncidentSectorSourcePatch
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ}

def map (P : PointIncidentSectorSourcePatch S p) : flatLinkSectorDisk P.angle P.radius → ℂ :=
  S.map ∘ P.sourceMap

theorem metric (P : PointIncidentSectorSourcePatch S p)
    (x z : flatLinkSectorDisk P.angle P.radius) :
    (pointSmoothConformalEDist a y (P.map x) (P.map z)).toReal = dist x z := by
  rw [map, Function.comp_apply, Function.comp_apply, S.metric]
  exact P.isometry.dist_eq x z

theorem range_iff (P : PointIncidentSectorSourcePatch S p) {z : ℂ}
    (hz : (pointSmoothConformalEDist a y z p).toReal ≤ P.radius) :
    z ∈ range S.map ↔ z ∈ range P.map := by
  constructor
  · rintro ⟨q, rfl⟩
    have he := S.metric q
      (P.sourceMap (flatLinkSectorDiskApex P.angle_pos.le P.radius_pos.le))
    rw [P.center] at he
    rw [he] at hz
    obtain ⟨x, hx⟩ := P.local_range q hz
    exact ⟨x, congrArg S.map hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨P.sourceMap x, rfl⟩

theorem mem_openImage (P : PointIncidentSectorSourcePatch S p)
    (x : flatLinkSectorDisk P.angle P.radius)
    (hx : x.1 ∈ _root_.interior (closedEuclideanSector P.angle))
    (hxim : 0 < x.1.im) (hxR : ‖x.1‖ < P.radius) : P.map x ∈ S.openImage :=
  ⟨P.sourceMap x, P.interior x hx hxim hxR, rfl⟩

/-- The orientation used to place the new piece is actually derived from
this retained source patch in the prescribed common chart. -/
theorem exists_directed_polar (P : PointIncidentSectorSourcePatch S p)
    (ha : ∀ j, 0 ≤ a j)
    (C : PointFlatLinkConeDisk a y
      (P.map (flatLinkSectorDiskApex P.angle_pos.le P.radius_pos.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ρ ≤ P.radius) (hρC : ρ ≤ C.radius) :
    ∃ lo : ℝ, ∃ forward : Bool, ∀ r (hr : r ∈ Icc (0 : ℝ) ρ) (t : unitInterval),
      C.chart (P.map (flatLinkSectorDiskPoint P.angle_pos.le P.angle_le_pi r
        ⟨hr.1, hr.2.trans hρP⟩ t)) =
        sectorPolar r (lo + flatLinkOrientedAngle forward
          (P.angle / (coalescedPointExponent a y
            (P.map (flatLinkSectorDiskApex P.angle_pos.le P.radius_pos.le)) / 2 + 1)) t) :=
  exists_pointFlatLinkDisk_fixed_chart_radial_polar ha y P.angle_pos P.angle_le_pi P.radius_pos
    P.map P.metric C hρ hρP hρC

end PointIncidentSectorSourcePatch

/-- Construct the retained source patch at every actual sector boundary
point. Its apex/passing classification and source-interior property are
conclusions of the construction. -/
theorem PointActualAllocatedSector.exists_incident_sourcePatch
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {p : ℂ}
    (hp : p ∈ range S.map) (hopen : p ∉ S.openImage) :
    Nonempty (PointIncidentSectorSourcePatch S p) := by
  classical
  obtain ⟨q, rfl⟩ := hp
  have hqinterior : q.1 ∉ interior (closedEuclideanSector S.beta) :=
    fun hq ↦ hopen ⟨q, hq, rfl⟩
  rcases closedEuclideanSector_noninterior_cases S.positive S.le_pi q hqinterior with
    hq0 | ⟨r, hr, top, hqray⟩
  · have hq : q = flatLinkSectorApex S.positive.le := Subtype.ext hq0
    subst q
    let inc : flatLinkSectorDisk S.beta 1 → closedEuclideanSector S.beta :=
      fun x ↦ ⟨x.1, x.2.1⟩
    refine ⟨{
      angle := S.beta, angle_pos := S.positive, angle_le_pi := S.le_pi,
      radius := 1, radius_pos := by norm_num, sourceMap := inc,
      isometry := Isometry.of_dist_eq (fun _ _ ↦ rfl), center := rfl,
      local_range := ?_, interior := fun x hx _ _ ↦ hx,
      angle_eq := by simp [PointActualAllocatedSector.apex]
    }⟩
    intro q hq
    have hn : ‖q.1‖ ≤ 1 := by simpa only [Subtype.dist_eq, inc,
      flatLinkSectorDiskApex, dist_zero_right] using hq
    exact ⟨⟨q.1, q.2, hn⟩, rfl⟩
  · obtain ⟨R, hR, _, hmem⟩ := exists_sectorEdge_centeredHalfDisk hr S.positive S.le_pi top
    let e := sectorEdgeChart top r S.beta
    have hK : ∀ w : ℂ, ‖w‖ ≤ R →
        (e w ∈ closedEuclideanSector S.beta ↔ 0 ≤ w.im) := hmem
    have he0 : e 0 = q.1 := by
      rw [hqray]
      simpa only [Complex.ofReal_zero, add_zero] using sectorEdgeChart_real top r S.beta 0
    have hq : q = centeredHalfDiskInclusion e hK
        (flatLinkSectorDiskApex Real.pi_pos.le hR.le) := Subtype.ext he0.symm
    have hnotapex : S.map q ≠ S.apex := by
      intro he
      have heq : q = flatLinkSectorApex S.positive.le := S.map_injective he
      have hn : ‖q.1‖ = 0 := by rw [heq]; simp [flatLinkSectorApex]
      rw [hqray, sectorPolar_norm hr.le] at hn
      exact hr.ne' hn
    subst q
    refine ⟨{
      angle := Real.pi, angle_pos := Real.pi_pos, angle_le_pi := le_rfl,
      radius := R, radius_pos := hR,
      sourceMap := centeredHalfDiskInclusion e hK,
      isometry := centeredHalfDiskInclusion_isometry e hK, center := rfl,
      local_range := ?_, interior := fun x _ hxim hxR ↦
        centeredHalfDiskInclusion_mem_interior e hK x hxR hxim,
      angle_eq := by rw [if_neg hnotapex]
    }⟩
    intro z hz
    rw [centeredHalfDiskInclusion_range]
    exact hz

end RepulsiveCoulomb
