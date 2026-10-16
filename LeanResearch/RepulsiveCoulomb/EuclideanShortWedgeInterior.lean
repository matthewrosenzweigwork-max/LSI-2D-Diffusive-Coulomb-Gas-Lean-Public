import LeanResearch.RepulsiveCoulomb.DirectedSectorDiskPlacement
import LeanResearch.RepulsiveCoulomb.EuclideanClosedSectorSource
import LeanResearch.RepulsiveCoulomb.EuclideanSectorBoundaryCases
import LeanResearch.RepulsiveCoulomb.PointActualSectorBottomIdentification
import LeanResearch.RepulsiveCoulomb.OrderedEuclideanWedgeCover
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! SOURCE-ONLY, UNCOMPILED. Ordinary positive short Euclidean wedges have
connected nonempty interiors dense in the whole closed wedge. Every interior
point has strictly positive radius and strictly interior ordered angle. This
is actual geometry of the literal target wedges used by finite surgery. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem flatLinkOccupiedDisk_eq_placed_disk {R lo hi : ℝ}
    (hR : 0 < R) (hw : 0 < hi - lo) (hwπ : hi - lo ≤ Real.pi) :
    flatLinkOccupiedDisk R lo hi =
      (directedSectorPlacement lo (hi-lo) true) '' flatLinkSectorDisk (hi-lo) R := by
  have h := directedSectorPlacement_disk_range hw hwπ hR lo true
  rw [show lo + (hi-lo) = hi by ring] at h
  rw [← h]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem flatLinkSectorDisk_convex {β R : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    Convex ℝ (flatLinkSectorDisk β R) := by
  have h := (closedEuclideanSector_convex hβ hβπ).inter (convex_closedBall (0 : ℂ) R)
  simpa only [flatLinkSectorDisk, closedBall, dist_zero_right] using h

theorem flatLinkOccupiedDisk_convex {R lo hi : ℝ}
    (hR : 0 < R) (hw : 0 < hi - lo) (hwπ : hi - lo ≤ Real.pi) :
    Convex ℝ (flatLinkOccupiedDisk R lo hi) := by
  rw [flatLinkOccupiedDisk_eq_placed_disk hR hw hwπ]
  exact Convex.affine_image
    (directedSectorPlacement lo (hi-lo) true).toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap
    (flatLinkSectorDisk_convex hw hwπ)

theorem flatLinkOccupiedDisk_interior_nonempty {R lo hi : ℝ}
    (hR : 0 < R) (hw : 0 < hi - lo) (hwπ : hi - lo ≤ Real.pi) :
    (interior (flatLinkOccupiedDisk R lo hi)).Nonempty := by
  rw [flatLinkOccupiedDisk_eq_placed_disk hR hw hwπ]
  change (interior ((directedSectorPlacement lo (hi-lo) true).toHomeomorph ''
    flatLinkSectorDisk (hi-lo) R)).Nonempty
  rw [← (directedSectorPlacement lo (hi-lo) true).toHomeomorph.image_interior]
  have h : (interior (flatLinkSectorDisk (hi-lo) R)).Nonempty :=
    retainedFlatSectorDisk_interior_nonempty hw hwπ hR
  exact h.image _

theorem flatLinkOccupiedDisk_closure_interior {R lo hi : ℝ}
    (hR : 0 < R) (hw : 0 < hi - lo) (hwπ : hi - lo ≤ Real.pi) :
    closure (interior (flatLinkOccupiedDisk R lo hi)) = flatLinkOccupiedDisk R lo hi :=
  ((flatLinkOccupiedDisk_convex hR hw hwπ).closure_interior_eq_closure_of_nonempty_interior
    (flatLinkOccupiedDisk_interior_nonempty hR hw hwπ)).trans
    (flatLinkOccupiedDisk_isClosed R lo hi).closure_eq

theorem flatLinkOccupiedDisk_interior_preconnected {R lo hi : ℝ}
    (hR : 0 < R) (hw : 0 < hi - lo) (hwπ : hi - lo ≤ Real.pi) :
    IsPreconnected (interior (flatLinkOccupiedDisk R lo hi)) :=
  (flatLinkOccupiedDisk_convex hR hw hwπ).interior.isPreconnected

theorem flatLinkOccupiedDisk_interior_strict_polar {R lo hi : ℝ}
    (hR : 0 < R) (hw : 0 < hi - lo) (hwπ : hi - lo ≤ Real.pi)
    {z : ℂ} (hz : z ∈ interior (flatLinkOccupiedDisk R lo hi)) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) R ∧ ∃ θ : ℝ, θ ∈ Ioo lo hi ∧ z = sectorPolar r θ := by
  rw [flatLinkOccupiedDisk_eq_placed_disk hR hw hwπ] at hz
  change z ∈ interior ((directedSectorPlacement lo (hi-lo) true).toHomeomorph ''
    flatLinkSectorDisk (hi-lo) R) at hz
  rw [← (directedSectorPlacement lo (hi-lo) true).toHomeomorph.image_interior] at hz
  obtain ⟨w, hwK, rfl⟩ := hz
  have hwS : w ∈ interior (closedEuclideanSector (hi-lo)) :=
    interior_mono inter_subset_left hwK
  have harg := closedEuclideanSector_interior_strict_arg hw hwπ hwS
  have hw0 : w ≠ 0 := by
    intro he
    have hh := harg.1
    rw [he, Complex.arg_zero] at hh
    exact lt_irrefl _ hh
  have hn : w ∈ interior (closedBall (0 : ℂ) R) :=
    interior_mono (show flatLinkSectorDisk (hi-lo) R ⊆ closedBall (0 : ℂ) R from
      fun q hq ↦ by simpa only [mem_closedBall, dist_zero_right, Set.mem_ofPred_eq] using hq.2) hwK
  rw [interior_closedBall (0 : ℂ) hR.ne'] at hn
  have hnR : ‖w‖ < R := by simpa only [mem_ball, dist_zero_right] using hn
  refine ⟨‖w‖, ⟨norm_pos_iff.mpr hw0, hnR⟩, lo + Complex.arg w,
    ⟨by linarith [harg.1], by linarith [harg.2]⟩, ?_⟩
  calc
    directedSectorPlacement lo (hi-lo) true w =
        directedSectorPlacement lo (hi-lo) true (sectorPolar ‖w‖ (Complex.arg w)) :=
      congrArg _ (sectorPolar_norm_arg w).symm
    _ = sectorPolar ‖w‖ (lo + Complex.arg w) := by
      rw [directedSectorPlacement_polar]
      rfl

end RepulsiveCoulomb
