module

public import LeanResearch.RepulsiveCoulomb.EuclideanSectorEdgeHalfDisk
public import LeanResearch.RepulsiveCoulomb.FlatLinkSectorDisk

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. An actual rigid recentering of a closed halfdisk
inside a closed sector. The range is proved to be exactly the intersection
with the centered closed ball. In particular this supplies the entire local
piece at a passing edge, not only an injective map into that piece. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The only input is a literal local halfplane membership computation. -/
def centeredHalfDiskInclusion {K : Set ℂ} {R : ℝ} (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im)) :
    flatLinkSectorDisk Real.pi R → K := fun w ↦
  ⟨e w.1, (hK w.1 w.2.2).mpr (by
    have hw : 0 ≤ w.1.im ∧ ‖w.1‖ ≤ R := by
      simpa only [flatLinkSectorDisk_pi, mem_setOf_eq] using w.2
    exact hw.1)⟩

@[simp] theorem centeredHalfDiskInclusion_val {K : Set ℂ} {R : ℝ}
    (e : ℂ ≃ᵢ ℂ) (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im))
    (w : flatLinkSectorDisk Real.pi R) :
    (centeredHalfDiskInclusion e hK w : ℂ) = e w.1 := rfl

theorem centeredHalfDiskInclusion_isometry {K : Set ℂ} {R : ℝ}
    (e : ℂ ≃ᵢ ℂ) (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im)) :
    Isometry (centeredHalfDiskInclusion e hK) := by
  apply Isometry.of_dist_eq
  intro w v
  exact e.dist_eq w.1 v.1

theorem centeredHalfDiskInclusion_range {K : Set ℂ} {R : ℝ}
    (e : ℂ ≃ᵢ ℂ) (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im)) :
    range (centeredHalfDiskInclusion e hK) = {z : K | dist z.1 (e 0) ≤ R} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change dist (e w.1) (e 0) ≤ R
    rw [e.dist_eq, dist_zero_right]
    exact w.2.2
  · intro hz
    let w : ℂ := e.symm z.1
    have hw : ‖w‖ ≤ R := by
      change ‖e.symm z.1‖ ≤ R
      rw [← dist_zero_right, ← e.dist_eq, e.apply_symm_apply]
      exact hz
    have him : 0 ≤ w.im := (hK w hw).mp (by
      simpa only [w, e.apply_symm_apply] using z.2)
    have hwD : w ∈ flatLinkSectorDisk Real.pi R := by
      rw [flatLinkSectorDisk_pi]
      exact ⟨him, hw⟩
    refine ⟨⟨w, hwD⟩, ?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply z.1

theorem centeredHalfDiskInclusion_center {K : Set ℂ} {R : ℝ}
    (hR : 0 ≤ R) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im)) :
    (centeredHalfDiskInclusion e hK
      (flatLinkSectorDiskApex Real.pi_pos.le hR) : ℂ) = e 0 := rfl

/-- Both nonapex sector edges have actual full centered halfdisk patches.
The chosen radius is smaller than the distance to the sector apex. -/
theorem exists_sectorEdge_centeredHalfDisk {r β : ℝ}
    (hr : 0 < r) (hβ : 0 < β) (hβπ : β ≤ Real.pi) (top : Bool) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧
      ∀ w : ℂ, ‖w‖ ≤ R →
        ((if top then sectorTopEdgeChart r β else sectorBottomEdgeChart r) w ∈
          closedEuclideanSector β ↔ 0 ≤ w.im) := by
  have hp : ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, ‖w‖ ≤ R →
      ((if top then sectorTopEdgeChart r β else sectorBottomEdgeChart r) w ∈
        closedEuclideanSector β ↔ 0 ≤ w.im) := by
    cases top
    · exact exists_sectorBottomEdgeChart_halfdisk hr hβ hβπ
    · exact exists_sectorTopEdgeChart_halfdisk hr hβ hβπ
  obtain ⟨R, hR, hmem⟩ := hp
  refine ⟨min R (r / 2), lt_min hR (half_pos hr),
    (min_le_right _ _).trans_lt (half_lt_self hr), fun w hw ↦ ?_⟩
  exact hmem w (hw.trans (min_le_left _ _))

end RepulsiveCoulomb
