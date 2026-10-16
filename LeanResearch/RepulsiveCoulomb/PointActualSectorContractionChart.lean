import LeanResearch.RepulsiveCoulomb.PointActualSectorIncidentOccupancy
import Mathlib.Topology.Homeomorph.Lemmas

/-! SOURCE-ONLY, UNCOMPILED. Actual continuous forward and inverse coordinates
on the physical closed sector image. The inverse of the original sector map
is constructed from its proved closed embedding. These are individual piece
coordinates, not an assumed chart on an ambient neighborhood. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointActualSectorContractionChart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    range S.map ≃ₜ closedEuclideanSector (c * S.beta) :=
  (S.isClosedEmbedding ha).isEmbedding.toHomeomorph.symm.trans
    (closedSectorContractionHomeomorph hc hc1 S.positive.le S.le_pi)

theorem pointActualSectorContractionChart_apply_map
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (q : closedEuclideanSector S.beta) :
    (pointActualSectorContractionChart ha S hc hc1 ⟨S.map q, mem_range_self q⟩ : ℂ) =
      sectorAngularMap c q.1 := by
  simp only [pointActualSectorContractionChart, Homeomorph.trans_apply,
    Topology.IsEmbedding.toHomeomorph_symm_apply]
  rfl

theorem pointActualSectorContractionChart_dist_bounds
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (x z : range S.map) :
    c * (pointSmoothConformalEDist a y x.1 z.1).toReal ≤
      dist (pointActualSectorContractionChart ha S hc hc1 x)
        (pointActualSectorContractionChart ha S hc hc1 z) ∧
      dist (pointActualSectorContractionChart ha S hc hc1 x)
        (pointActualSectorContractionChart ha S hc hc1 z) ≤
        (pointSmoothConformalEDist a y x.1 z.1).toReal := by
  obtain ⟨u, hu⟩ := x.2
  obtain ⟨v, hv⟩ := z.2
  have hx : x = ⟨S.map u, mem_range_self u⟩ := Subtype.ext hu.symm
  have hz : z = ⟨S.map v, mem_range_self v⟩ := Subtype.ext hv.symm
  rw [hx, hz, S.metric]
  change c * dist u v ≤ dist
      (pointActualSectorContractionChart ha S hc hc1 ⟨S.map u, _⟩ : ℂ)
      (pointActualSectorContractionChart ha S hc hc1 ⟨S.map v, _⟩ : ℂ) ∧
    dist (pointActualSectorContractionChart ha S hc hc1 ⟨S.map u, _⟩ : ℂ)
      (pointActualSectorContractionChart ha S hc hc1 ⟨S.map v, _⟩ : ℂ) ≤ dist u v
  rw [pointActualSectorContractionChart_apply_map, pointActualSectorContractionChart_apply_map]
  simpa only [Subtype.dist_eq, dist_eq_norm] using
    sectorAngularMap_dist_bounds hc.le hc1 S.le_pi u.2 v.2

/-- Actual inverse on a centered new halfdisk in the contracted sector. -/
def pointActualContractedHalfDiskMap
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * S.beta) ↔ 0 ≤ w.im)) :
    flatLinkSectorDisk Real.pi R → ℂ :=
  S.map ∘ contractedCenteredHalfDiskInclusion hc hc1 S.positive.le S.le_pi e hK

theorem pointActualContractedHalfDiskMap_continuous
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * S.beta) ↔ 0 ≤ w.im)) :
    Continuous (pointActualContractedHalfDiskMap S hc hc1 e hK) :=
  (S.isClosedEmbedding ha).continuous.comp
    (contractedCenteredHalfDiskInclusion_continuous hc hc1 S.positive.le S.le_pi e hK)

theorem pointActualContractedHalfDiskMap_dist_bounds
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * S.beta) ↔ 0 ≤ w.im))
    (x z : flatLinkSectorDisk Real.pi R) :
    c * (pointSmoothConformalEDist a y
      (pointActualContractedHalfDiskMap S hc hc1 e hK x)
      (pointActualContractedHalfDiskMap S hc hc1 e hK z)).toReal ≤ dist x z ∧
      dist x z ≤ (pointSmoothConformalEDist a y
        (pointActualContractedHalfDiskMap S hc hc1 e hK x)
        (pointActualContractedHalfDiskMap S hc hc1 e hK z)).toReal := by
  simp only [pointActualContractedHalfDiskMap, Function.comp_apply, S.metric]
  exact contractedCenteredHalfDiskInclusion_dist_bounds hc hc1 S.positive.le S.le_pi e hK x z

/-- The explicit inverse lies in the genuine old open ball whenever its new
radius is less than c times that ball's radius. This is the clearance needed
to glue inverse branches before obtaining an ambient open chart. -/
theorem pointActualContractedHalfDiskMap_small_radius
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c R δ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 ≤ R) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * S.beta) ↔ 0 ≤ w.im))
    (w : flatLinkSectorDisk Real.pi R) (hw : ‖w.1‖ < c * δ) :
    (pointSmoothConformalEDist a y (pointActualContractedHalfDiskMap S hc hc1 e hK w)
      (pointActualContractedHalfDiskMap S hc hc1 e hK
        (flatLinkSectorDiskApex Real.pi_pos.le hR))).toReal < δ := by
  have hb := (pointActualContractedHalfDiskMap_dist_bounds S hc hc1 e hK w
    (flatLinkSectorDiskApex Real.pi_pos.le hR)).1
  change c * _ ≤ dist w.1 (0 : ℂ) at hb
  rw [dist_zero_right] at hb
  nlinarith [hb.trans_lt hw]

end RepulsiveCoulomb
