module

public import LeanResearch.RepulsiveCoulomb.DirectedSectorDiskPlacement

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. An actual small ordered target wedge maps
continuously into a branch's larger canonical Euclidean sector disk. The
radius comparison and the exact inverse-placement identity are proved. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def directedSectorDiskRestriction {β r R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 < r) (hrR : r ≤ R)
    (lo : ℝ) (forward : Bool) : flatLinkOccupiedDisk r lo (lo + β) → flatLinkSectorDisk β R :=
  fun z ↦ ⟨(directedSectorPlacement lo β forward).symm z.1,
    ((directedSectorPlacement_mem_disk_iff hβ hβπ hr lo forward z.1).mp z.2).1,
    ((directedSectorPlacement_mem_disk_iff hβ hβπ hr lo forward z.1).mp z.2).2.trans hrR⟩

theorem directedSectorDiskRestriction_continuous {β r R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 < r) (hrR : r ≤ R)
    (lo : ℝ) (forward : Bool) :
    Continuous (directedSectorDiskRestriction hβ hβπ hr hrR lo forward) :=
  ((directedSectorPlacement lo β forward).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem directedSectorDiskRestriction_norm {β r R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 < r) (hrR : r ≤ R)
    (lo : ℝ) (forward : Bool) (z : flatLinkOccupiedDisk r lo (lo + β)) :
    ‖(directedSectorDiskRestriction hβ hβπ hr hrR lo forward z).1‖ = ‖z.1‖ :=
  directedSectorPlacement_symm_norm lo β forward z.1

theorem directedSectorDiskRestriction_placed {β r R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 < r) (hrR : r ≤ R)
    (lo : ℝ) (forward : Bool) (z : flatLinkOccupiedDisk r lo (lo + β)) :
    directedSectorPlacement lo β forward
      (directedSectorDiskRestriction hβ hβπ hr hrR lo forward z).1 = z.1 :=
  (directedSectorPlacement lo β forward).apply_symm_apply z.1

end RepulsiveCoulomb
