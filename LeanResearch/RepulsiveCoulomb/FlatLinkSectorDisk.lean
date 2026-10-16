module

public import LeanResearch.RepulsiveCoulomb.SectorVariation

@[expose] public section

/-! Isolated, uncompiled author draft. Literal bounded source sectors. In
particular beta = pi is a closed Euclidean halfdisk, with its center on the
straight boundary. It models a passing edge after an ordinary rigid recentering. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def flatLinkSectorDisk (β L : ℝ) : Set ℂ :=
  closedEuclideanSector β ∩ {z | ‖z‖ ≤ L}

/-- The passing-edge source is literally the upper closed Euclidean halfdisk. -/
theorem flatLinkSectorDisk_pi (L : ℝ) :
    flatLinkSectorDisk Real.pi L = {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ L} := by
  ext z
  simp only [flatLinkSectorDisk, closedEuclideanSector, mem_inter_iff, mem_setOf_eq,
    Complex.arg_nonneg_iff, Complex.arg_le_pi, and_true]

def flatLinkSectorDiskApex {β L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L) :
    flatLinkSectorDisk β L := ⟨0, by simp [flatLinkSectorDisk, closedEuclideanSector, hβ, hL]⟩

theorem flatLink_polar_mem_sector {β r : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hr : 0 ≤ r) (t : unitInterval) : sectorPolar r (β * t.1) ∈ closedEuclideanSector β := by
  by_cases hr0 : r = 0
  · simp [hr0, sectorPolar_zero, closedEuclideanSector, hβ]
  · have hangle : β * t.1 ∈ Ioc (-Real.pi) Real.pi :=
      ⟨(neg_neg_of_pos Real.pi_pos).trans_le (mul_nonneg hβ t.2.1),
        (mul_le_of_le_one_right hβ t.2.2).trans hβπ⟩
    change 0 ≤ Complex.arg (sectorPolar r (β * t.1)) ∧
      Complex.arg (sectorPolar r (β * t.1)) ≤ β
    rw [sectorPolar_arg (lt_of_le_of_ne hr (Ne.symm hr0)) hangle]
    exact ⟨mul_nonneg hβ t.2.1, mul_le_of_le_one_right hβ t.2.2⟩

def flatLinkSectorDiskPoint {β L : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) L) (t : unitInterval) : flatLinkSectorDisk β L :=
  ⟨sectorPolar r (β * t.1), flatLink_polar_mem_sector hβ hβπ hr.1 t,
    by simpa only [mem_setOf_eq, sectorPolar_norm hr.1] using hr.2⟩

@[simp] theorem flatLinkSectorDiskPoint_coe {β L : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) L) (t : unitInterval) :
    (flatLinkSectorDiskPoint hβ hβπ r hr t : ℂ) = sectorPolar r (β * t.1) := rfl

@[simp] theorem flatLinkSectorDiskPoint_zero {β L : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hL : 0 ≤ L) (t : unitInterval) :
    flatLinkSectorDiskPoint hβ hβπ 0 ⟨le_rfl, hL⟩ t = flatLinkSectorDiskApex hβ hL := by
  apply Subtype.ext
  exact sectorPolar_zero _

theorem continuous_flatLinkSectorDiskPoint {β L r : ℝ} (hβ : 0 ≤ β)
    (hβπ : β ≤ Real.pi) (hr : r ∈ Icc (0 : ℝ) L) :
    Continuous (flatLinkSectorDiskPoint hβ hβπ r hr) := by
  unfold flatLinkSectorDiskPoint
  apply Continuous.subtype_mk
  simp only [sectorPolar, conePhase]
  fun_prop

/-- Exact source coverage at a smaller radius; the representation includes
both angular endpoints, the outer circular edge, and the center. -/
theorem flatLinkSectorDisk_representation {β L ρ : ℝ} (hβ : 0 < β)
    (hβπ : β ≤ Real.pi) (hρ : 0 < ρ) (hρL : ρ ≤ L)
    (x : flatLinkSectorDisk β L) (hx : ‖x.1‖ ≤ ρ) :
    ∃ s t : unitInterval, x = flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
      ⟨mul_nonneg hρ.le s.2.1, (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t := by
  let s : unitInterval := ⟨‖x.1‖ / ρ, div_nonneg (norm_nonneg _) hρ.le,
    (div_le_one hρ).mpr hx⟩
  let t : unitInterval := ⟨Complex.arg x.1 / β, div_nonneg x.2.1.1 hβ.le,
    (div_le_one hβ).mpr x.2.1.2⟩
  refine ⟨s, t, ?_⟩
  apply Subtype.ext
  change x.1 = sectorPolar (ρ * (‖x.1‖ / ρ)) (β * (Complex.arg x.1 / β))
  rw [mul_div_cancel₀ _ hρ.ne', mul_div_cancel₀ _ hβ.ne', sectorPolar_norm_arg]

/-- The target occupied set is a literal unwrapped angular interval, including
its two radial edges and center. Its width is recorded separately in physical
angle units. -/
def flatLinkOccupiedDisk (ρ lo hi : ℝ) : Set ℂ :=
  {w | ∃ r ∈ Icc (0 : ℝ) ρ, ∃ θ ∈ Icc lo hi, w = sectorPolar r θ}

end RepulsiveCoulomb
