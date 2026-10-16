import LeanResearch.RepulsiveCoulomb.PointConstructedRefinedAngles
import LeanResearch.RepulsiveCoulomb.PointPairedSectorSurgeryCoordinates
import LeanResearch.RepulsiveCoulomb.PointFiniteIncidentLinkModel

/-! SOURCE-ONLY, UNCOMPILED. Construct all common local input from the
actual finite allocation. The paired old/new source coordinates are chosen
first and retained; the common polar order is derived from those very maps.
All nonincident closed sectors are excluded by the same positive radius. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Indexed closed/open disjointness survives concatenation of actual
halfplane allocations. Only their proved listwise disjointness and interior
regularity are used. -/
theorem pointAllocatedList_incident_closed_disjoint
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y))
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) →
        coalescedPointExponent a y (S.map z) = 0)
    (p : ℂ) (i j : PointIncidentIndex L p) (hij : i ≠ j) :
    Disjoint (range (L.get i.1).map) (L.get j.1).openImage := by
  have hne : i.1 ≠ j.1 := fun he ↦ hij (Subtype.ext he)
  have hd : Disjoint (L.get i.1).openImage (L.get j.1).openImage := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdis.rel_get_of_lt h
    · exact (hdis.rel_get_of_lt h).symm
  rw [← (L.get i.1).closure_openImage ha]
  exact hd.closure_left (pointFlatEmbedding_isOpen_openImage ha y (L.get j.1).map
    (L.get j.1).metric (hregular _ (List.get_mem L j.1)))

structure PointFiniteSurgeryIncidentData
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) (c : ℝ) where
  cone : PointFlatLinkConeDisk a y p
  paired : ∀ i : PointIncidentIndex L p, PointPairedSectorSurgeryCoordinates (L.get i.1) p c
  radius : ℝ
  radius_pos : 0 < radius
  radius_cone : radius ≤ cone.radius
  radius_old : ∀ i, radius ≤ (paired i).old.radius
  radius_new : ∀ i, radius ≤ (paired i).new.radius
  nonincident_clear : ∀ i : Fin L.length, p ∉ range (L.get i).map →
    ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ radius → z ∉ range (L.get i).map
  lo : PointIncidentIndex L p → ℝ
  forward : PointIncidentIndex L p → Bool
  polar : ∀ i, (paired i).sourcePatch.PolarAt cone (radius_old i) (lo i) (forward i)

/-- No final chart, endpoint partition, or branch law is assumed here. -/
theorem exists_pointFiniteSurgeryIncidentData
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y)) (p : ℂ)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hseam : ∀ i : Fin L.length, p ∉ (L.get i).openImage) :
    Nonempty (PointFiniteSurgeryIncidentData L p c) := by
  classical
  obtain ⟨C⟩ := exists_pointFlatLinkConeDisk ha y p
  have hpaired : ∀ i : PointIncidentIndex L p,
      Nonempty (PointPairedSectorSurgeryCoordinates (L.get i.1) p c) :=
    fun i ↦ (L.get i.1).exists_paired_surgery_coordinates hc hc1 i.2 (hseam i.1)
  let B := fun i : PointIncidentIndex L p ↦ Classical.choice (hpaired i)
  obtain ⟨r, hr, hrC, oldlo, hmodel⟩ :=
    exists_pointFiniteSector_common_incident_link ha y (fun i : Fin L.length ↦ L.get i) p hseam C
  let radii : Finset ℝ := insert r
    ((Finset.univ.image (fun i : PointIncidentIndex L p ↦ (B i).old.radius)) ∪
      (Finset.univ.image (fun i : PointIncidentIndex L p ↦ (B i).new.radius)))
  have hnonempty : radii.Nonempty := ⟨r, Finset.mem_insert_self _ _⟩
  let R := radii.min' hnonempty
  have hR : 0 < R := by
    apply (radii.lt_min'_iff hnonempty).mpr
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hr
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (B i).old.radius_pos
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact (B i).new.radius_pos
  have hRr : R ≤ r := radii.min'_le _ (Finset.mem_insert_self _ _)
  have hRold (i : PointIncidentIndex L p) : R ≤ (B i).old.radius :=
    radii.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  have hRnew (i : PointIncidentIndex L p) : R ≤ (B i).new.radius :=
    radii.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  have hpol : ∀ i : PointIncidentIndex L p, ∃ lo : ℝ, ∃ forward : Bool,
      (B i).sourcePatch.PolarAt C (hRold i) lo forward :=
    fun i ↦ (B i).sourcePatch.exists_polarAt ha C hR (hRold i) (hRr.trans hrC)
  choose lo forward hpolar using hpol
  refine ⟨{
    cone := C, paired := B, radius := R, radius_pos := hR,
    radius_cone := hRr.trans hrC, radius_old := hRold, radius_new := hRnew,
    nonincident_clear := ?_, lo := lo, forward := forward, polar := hpolar
  }⟩
  intro i hi z hz hzi
  exact hi ((hmodel i z (hz.trans hRr)).mp hzi).1

end RepulsiveCoulomb
