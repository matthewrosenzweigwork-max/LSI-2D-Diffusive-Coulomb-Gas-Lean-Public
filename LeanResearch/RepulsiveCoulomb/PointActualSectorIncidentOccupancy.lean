import LeanResearch.RepulsiveCoulomb.PointFiniteSectorLocalGeometry
import LeanResearch.RepulsiveCoulomb.EuclideanSectorBoundaryCases
import LeanResearch.RepulsiveCoulomb.ContractedPassingEdgeHalfDisk

/-! SOURCE-ONLY, UNCOMPILED. Each actual incident sector at a seam point is
classified from its literal source. Its full local image is then an actual
occupied interval in one prescribed common cone chart. The width is beta at
its own apex and pi at a passing edge. No incident-piece model or chart
occupancy is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointClosedSectorDiskRestriction {β R : ℝ}
    (f : closedEuclideanSector β → ℂ) : flatLinkSectorDisk β R → ℂ :=
  fun w ↦ f ⟨w.1, w.2.1⟩

theorem exists_pointClosedSector_apex_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (f : closedEuclideanSector β → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorApex hβ.le))) :
    ∃ lo : ℝ, ∀ z,
      (pointSmoothConformalEDist a y z (f (flatLinkSectorApex hβ.le))).toReal ≤ C.radius →
      (z ∈ range f ↔ C.chart z ∈ flatLinkOccupiedDisk C.radius lo
        (lo + β / (coalescedPointExponent a y (f (flatLinkSectorApex hβ.le)) / 2 + 1))) := by
  let g : flatLinkSectorDisk β C.radius → ℂ := pointClosedSectorDiskRestriction f
  have hg : ∀ x z, (pointSmoothConformalEDist a y (g x) (g z)).toReal = dist x z := by
    intro x z
    exact hd ⟨x.1, x.2.1⟩ ⟨z.1, z.2.1⟩
  obtain ⟨lo, hlo⟩ := exists_pointFlatLinkDisk_fixed_chart_occupancy ha y
    hβ hβπ C.radius_pos g hg C C.radius_pos le_rfl le_rfl
  refine ⟨lo, fun z hz ↦ ?_⟩
  have hrange : z ∈ range f ↔ z ∈ range g := by
    constructor
    · rintro ⟨q, rfl⟩
      have hqn : ‖q.1‖ ≤ C.radius := by
        simpa only [hd, Subtype.dist_eq, flatLinkSectorApex, dist_zero_right] using hz
      exact ⟨⟨q.1, q.2, hqn⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⟨q.1, q.2.1⟩, rfl⟩
  exact hrange.trans (hlo z hz)

theorem PointActualAllocatedSector.map_injective
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} (S : PointActualAllocatedSector a y) :
    Function.Injective S.map := by
  intro x z he
  apply dist_eq_zero.mp
  rw [← S.metric, he, pointSmoothConformalEDist_self, ENNReal.toReal_zero]

/-- Actual full-range occupancy at every incident boundary point, in the
fixed ambient chart C. Its radius is constructed by the literal edge geometry.
The exterior complement is not claimed to be covered by selected sectors. -/
theorem PointActualAllocatedSector.exists_incident_fixed_chart_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (S : PointActualAllocatedSector a y) {p : ℂ}
    (hp : p ∈ range S.map) (hopen : p ∉ S.openImage)
    (C : PointFlatLinkConeDisk a y p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ C.radius ∧ ∃ lo : ℝ,
      ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ range S.map ↔ C.chart z ∈ flatLinkOccupiedDisk ρ lo
          (lo + (if p = S.apex then S.beta else Real.pi) /
            (coalescedPointExponent a y p / 2 + 1))) := by
  classical
  obtain ⟨q, rfl⟩ := hp
  have hqinterior : q.1 ∉ interior (closedEuclideanSector S.beta) := by
    intro hq
    exact hopen ⟨q, hq, rfl⟩
  rcases closedEuclideanSector_noninterior_cases S.positive S.le_pi q hqinterior with
    hq0 | ⟨r, hr, top, hqray⟩
  · have hq : q = flatLinkSectorApex S.positive.le := Subtype.ext hq0
    subst q
    obtain ⟨lo, hlo⟩ := exists_pointClosedSector_apex_occupancy ha y S.positive S.le_pi
      S.map S.metric C
    refine ⟨C.radius, C.radius_pos, le_rfl, lo, ?_⟩
    simpa only [PointActualAllocatedSector.apex, if_pos rfl, ite_true] using hlo
  · obtain ⟨R, hR, hRr, hmem⟩ :=
      exists_sectorEdge_centeredHalfDisk hr S.positive S.le_pi top
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
    let ρ := min R C.radius
    have hρ : 0 < ρ := lt_min hR C.radius_pos
    obtain ⟨lo, hlo⟩ := exists_pointPassingEdge_fixed_chart_occupancy ha y hR S.map e hK
      S.metric C hρ (min_le_left _ _) (min_le_right _ _)
    refine ⟨ρ, hρ, min_le_right _ _, lo, ?_⟩
    simpa only [if_neg hnotapex, pointCenteredHalfDiskMap, Function.comp_apply] using hlo

end RepulsiveCoulomb
