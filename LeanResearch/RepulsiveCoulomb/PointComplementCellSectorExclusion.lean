module

public import LeanResearch.RepulsiveCoulomb.PointConstructedIncidentSurgeryChart
public import LeanResearch.RepulsiveCoulomb.PointActualSectorBottomIdentification

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual complement-cell exclusion.

The strict-radius part of a Euclidean source patch preserves sector interior
in both directions. Consequently its two endpoint rays are outside the
original selected sector's open image. Refined angular overlap identifies
every possible intersection of an unowned cell with an incident occupied
cell with one of these actual endpoint rays. Nonincident sectors are excluded
by the common radius. No complement-exclusion or seam-clearance field is
assumed.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

namespace EuclideanSectorDiskPatch

/-- The reverse interior implication follows from local membership and the
actual ambient placement; it is not a new field of the patch. -/
theorem inclusion_interior_iff {β : ℝ} (Q : EuclideanSectorDiskPatch β)
    (w : flatLinkSectorDisk Q.angle Q.radius) (hwR : ‖w.1‖ < Q.radius) :
    (Q.inclusion w).1 ∈ interior (closedEuclideanSector β) ↔
      w.1 ∈ interior (closedEuclideanSector Q.angle) := by
  constructor
  · intro hw
    let U : Set ℂ := Q.placement ⁻¹' interior (closedEuclideanSector β) ∩ ball 0 Q.radius
    have hU : IsOpen U :=
      (isOpen_interior.preimage Q.placement.continuous).inter isOpen_ball
    have hsub : U ⊆ closedEuclideanSector Q.angle := by
      intro z hz
      have hzn : ‖z‖ ≤ Q.radius := by
        have hh : dist z 0 < Q.radius := hz.2
        simpa only [dist_zero_right] using hh.le
      exact (Q.membership z hzn).mp (interior_subset hz.1)
    have hwU : w.1 ∈ U :=
      ⟨hw, by simpa only [mem_ball, dist_zero_right] using hwR⟩
    exact interior_mono hsub (by simpa only [hU.interior_eq] using hwU)
  · exact fun hw ↦ Q.inclusion_mem_interior w hw hwR

end EuclideanSectorDiskPatch

/-- Both closed sector endpoints, including their common apex, are excluded
from the planar interior. -/
theorem sectorPolar_endpoint_not_mem_interior {β r : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 ≤ r)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    sectorPolar r (β * t.1) ∉ interior (closedEuclideanSector β) := by
  intro hmem
  have harg := closedEuclideanSector_interior_strict_arg hβ hβπ hmem
  by_cases hr0 : r = 0
  · subst r
    rw [sectorPolar_zero, Complex.arg_zero] at harg
    exact lt_irrefl _ harg.1
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rcases ht with rfl | rfl
  · have ha : Complex.arg (sectorPolar r (β * (0 : unitInterval).1)) = 0 := by
      change Complex.arg (sectorPolar r (β * 0)) = 0
      rw [mul_zero]
      exact sectorPolar_arg hrpos ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
    rw [ha] at harg
    exact lt_irrefl _ harg.1
  · have ha : Complex.arg (sectorPolar r (β * (1 : unitInterval).1)) = β := by
      change Complex.arg (sectorPolar r (β * 1)) = β
      rw [mul_one]
      exact sectorPolar_arg hrpos ⟨by linarith [Real.pi_pos], hβπ⟩
    rw [ha] at harg
    exact lt_irrefl _ harg.2

namespace PointPairedSectorSurgeryCoordinates
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ} {c : ℝ}

/-- The actual source-patch endpoints are outside the selected open image.
Only source-map injectivity and the proved local interior equivalence enter. -/
theorem source_endpoint_not_mem_openImage (B : PointPairedSectorSurgeryCoordinates S p c)
    (r : ℝ) (hr : 0 ≤ r) (hrR : r < B.old.radius)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    B.sourcePatch.map
      (flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r ⟨hr, hrR.le⟩ t)
      ∉ S.openImage := by
  let q := flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r ⟨hr, hrR.le⟩ t
  rintro ⟨v, hv, hve⟩
  have hvq : v = B.old.inclusion q := S.map_injective hve
  have hq : (B.old.inclusion q).1 ∈ interior (closedEuclideanSector S.beta) := hvq ▸ hv
  have hqn : ‖q.1‖ < B.old.radius := by
    change ‖sectorPolar r (B.old.angle * t.1)‖ < B.old.radius
    rwa [sectorPolar_norm hr]
  have hqi := (B.old.inclusion_interior_iff q hqn).mp hq
  exact sectorPolar_endpoint_not_mem_interior B.old.angle_pos B.old.angle_le_pi hr t ht hqi

/-- An endpoint in the normalized old cone chart is an actual physical
source endpoint. This includes the center with radial parameter zero. -/
theorem rotated_endpoint_not_mem_openImage (B : PointPairedSectorSurgeryCoordinates S p c)
    (C : PointFlatLinkConeDisk a y p) {R : ℝ}
    (hRold : R ≤ B.old.radius) (hRC : R ≤ C.radius)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin : ℝ) {z : ℂ} (hz : z ∈ pointConeOpenBall (C.rotate (-origin)) R)
    (r : ℝ) (hr : 0 ≤ r) (top : Bool)
    (he : (C.rotate (-origin)).chart z = sectorPolar r
      (normalizedIncidentLower origin lo +
        if top then B.old.angle / (coalescedPointExponent a y p / 2 + 1) else 0)) :
    z ∉ S.openImage := by
  let D := C.rotate (-origin)
  let t := occupiedBranchEndpointParameter forward top
  have hrR : r < R := by
    have hn : ‖D.chart z‖ < R := by
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hz.2
    rwa [he, sectorPolar_norm hr] at hn
  let q := flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r
    ⟨hr, hrR.le.trans hRold⟩ t
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
    exact hqd.le.trans (hrR.le.trans hRC)
  have hqchart : D.chart (B.sourcePatch.map q) = D.chart z := by
    rw [he]
    simpa only [q, t, D, sourcePatch, PointIncidentSectorSourcePatch.map,
      Function.comp_apply, occupiedBranchEndpointParameter_angle] using
      B.sourcePatch.rotated_normalized_polarAt C hpolar origin r ⟨hr, hrR.le⟩ t
  have hqz : B.sourcePatch.map q = z := D.chart.injOn hqS hz.1 hqchart
  rw [← hqz]
  exact B.source_endpoint_not_mem_openImage r hr (hrR.trans_le hRold) t
    (occupiedBranchEndpointParameter_boundary forward top)

end PointPairedSectorSurgeryCoordinates

namespace PointConstructedIncidentSurgeryChart
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {p : ℂ} {c : ℝ} {hc : 0 < c} {hc1 : c ≤ 1}

/-- A refined cell belonging to a different coarse cell cannot meet an
incident selected open sector, even on its endpoint rays. -/
theorem sourceCell_not_mem_incident_openImage
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : Σ j : Fin D.N, Fin (D.refinement.count j))
    (i : PointIncidentIndex L p) (hxi : x.1 ≠ D.owner i)
    {z : ℂ}
    (hz : z ∈ pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius)
    (hzx : z ∈ pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial))
      D.data.radius D.refinement x) :
    z ∉ (L.get i.1).openImage := by
  let C := D.data.cone.rotate (-D.data.lo D.initial)
  let B := D.data.paired i
  have hRC : D.data.radius ≤ C.radius := D.data.radius_cone
  have hd := (mem_pointConeOpenBall_iff C hRC z).mp hz
  have hend (r : ℝ) (hr : 0 ≤ r) (top : Bool)
      (he : C.chart z = sectorPolar r
        (normalizedIncidentLower (D.data.lo D.initial) (D.data.lo i) +
          if top then B.old.angle / (coalescedPointExponent a y p / 2 + 1) else 0)) :
      z ∉ (L.get i.1).openImage :=
    B.rotated_endpoint_not_mem_openImage D.data.cone (D.data.radius_old i)
      D.data.radius_cone (D.data.polar i) (D.data.lo D.initial) hz r hr top he
  by_cases hz0 : C.chart z = 0
  · exact hend 0 le_rfl false (by simpa only [sectorPolar_zero] using hz0)
  intro hopen
  have hzr : z ∈ range (L.get i.1).map := by
    obtain ⟨q, _, hq⟩ := hopen
    exact ⟨q, hq⟩
  let v : Fin (D.refinement.count (D.owner i)) := ⟨0, D.refinement.count_pos _⟩
  let w : Σ j : Fin D.N, Fin (D.refinement.count j) := ⟨D.owner i, v⟩
  have hcount : D.refinement.count (D.owner i) = 1 :=
    D.refinement.occupied_whole _ (mem_range_self i)
  have hvfirst : v.castSucc = (0 : Fin (D.refinement.count (D.owner i) + 1)) :=
    Fin.ext rfl
  have hvlast : v.succ = Fin.last (D.refinement.count (D.owner i)) := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    change 0 + 1 = D.refinement.count (D.owner i)
    omega
  have hlo : D.refinement.node w.1 w.2.castSucc =
      normalizedIncidentLower (D.data.lo D.initial) (D.data.lo i) := by
    change D.refinement.node (D.owner i) v.castSucc = _
    rw [hvfirst, D.refinement.first]
    exact (D.owner_ends i).1
  have hhi : D.refinement.node w.1 w.2.succ =
      normalizedIncidentLower (D.data.lo D.initial) (D.data.lo i) +
        B.old.angle / (coalescedPointExponent a y p / 2 + 1) := by
    change D.refinement.node (D.owner i) v.succ = _
    rw [hvlast, D.refinement.last]
    exact (D.owner_ends i).2
  have hzw : C.chart z ∈ flatLinkOccupiedDisk D.data.radius
      (D.refinement.node w.1 w.2.castSucc) (D.refinement.node w.1 w.2.succ) := by
    rw [hlo, hhi]
    exact (B.sourcePatch.rotated_normalized_range_iff ha D.data.cone D.data.radius_pos
      (D.data.radius_old i) D.data.radius_cone (D.data.polar i)
      (D.data.lo D.initial) hd.le).mp hzr
  have hxw : x ≠ w := fun h ↦ hxi (congrArg Sigma.fst h)
  obtain ⟨r, hr, b, top, _, he⟩ := refinedIncident_source_overlap_endpoints
    D.refinement D.u_mono D.u_first D.u_last x w hxw hz0 hzx hzw
  have he' : C.chart z = sectorPolar r
      (normalizedIncidentLower (D.data.lo D.initial) (D.data.lo i) +
        if top then B.old.angle / (coalescedPointExponent a y p / 2 + 1) else 0) := by
    cases top <;> simpa only [refinedIncidentSourceEndpoint, Bool.false_eq_true,
      if_false, if_true, hlo, hhi, add_zero] using he
  exact hend r hr.le top he' hopen

/-- Every actual complement cell avoids all selected open sectors. This is
the whole finite-list exclusion needed by unchanged overlap geometry. -/
theorem complementCell_not_mem_openImage
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : Σ j : Fin D.N, Fin (D.refinement.count j))
    (hx : x.1 ∉ range D.owner) {z : ℂ}
    (hz : z ∈ pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius)
    (hzx : z ∈ pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial))
      D.data.radius D.refinement x) :
    ∀ i : Fin L.length, z ∉ (L.get i).openImage := by
  intro i
  by_cases hpi : p ∈ range (L.get i).map
  · let j : PointIncidentIndex L p := ⟨i, hpi⟩
    exact D.sourceCell_not_mem_incident_openImage x j
      (fun he ↦ hx ⟨j, he.symm⟩) hz hzx
  · have hd := (mem_pointConeOpenBall_iff
      (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius_cone z).mp hz
    intro hopen
    obtain ⟨q, _, hq⟩ := hopen
    exact D.data.nonincident_clear i hpi z hd.le ⟨q, hq⟩

end PointConstructedIncidentSurgeryChart
end RepulsiveCoulomb
