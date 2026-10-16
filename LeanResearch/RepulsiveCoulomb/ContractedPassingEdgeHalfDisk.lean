import LeanResearch.RepulsiveCoulomb.EuclideanCenteredHalfDisk
import LeanResearch.RepulsiveCoulomb.ClosedSectorContractionHomeomorph

/-! SOURCE-ONLY, UNCOMPILED. Actual post-contraction passing-edge charts.
The target halfdisk is centered at the contracted edge point; its source
parameterization uses the inverse of the actual angular contraction. Thus
its new angle is pi, never c*pi. Both signed directions on the seam keep
their arclength from the passing point. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def sectorEdgeChart (top : Bool) (r β : ℝ) : ℂ ≃ᵢ ℂ :=
  if top then sectorTopEdgeChart r β else sectorBottomEdgeChart r

theorem sectorEdgeChart_real (top : Bool) (r β t : ℝ) :
    sectorEdgeChart top r β (t : ℂ) =
      sectorPolar (r + t) (if top then β else 0) := by
  cases top
  · simp only [sectorEdgeChart, Bool.false_eq_true, ↓reduceIte,
      sectorBottomEdgeChart_apply, sectorPolar, conePhase]
    simp [Complex.ofReal_add, add_comm]
  · change conePhase β * star (t : ℂ) + sectorPolar r β = sectorPolar (r + t) β
    simp only [Complex.star_def, Complex.conj_ofReal, sectorPolar, Complex.ofReal_add]
    ring

theorem sectorAngularMap_sectorEdgeChart_real {c β r t : ℝ}
    (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) (hrt : 0 ≤ r + t) (top : Bool) :
    sectorAngularMap c (sectorEdgeChart top r β (t : ℂ)) =
      sectorEdgeChart top r (c * β) (t : ℂ) := by
  rw [sectorEdgeChart_real, sectorEdgeChart_real]
  cases top
  · simpa only [Bool.false_eq_true, ↓reduceIte, mul_zero] using
      (sectorAngularMap_polar (L := c) hrt
        (show (0 : ℝ) ∈ Ioc (-Real.pi) Real.pi from
          ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos.le⟩))
  · exact sectorAngularMap_polar hrt
      ⟨(neg_neg_of_pos Real.pi_pos).trans_le hβ, hβπ⟩

/-- A literal halfdisk in the contracted sector, pulled back by the actual
inverse homeomorphism. Its parameter is a new Euclidean coordinate. -/
def contractedCenteredHalfDiskInclusion {c β R : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * β) ↔ 0 ≤ w.im)) :
    flatLinkSectorDisk Real.pi R → closedEuclideanSector β :=
  (closedSectorContractionHomeomorph hc hc1 hβ hβπ).symm ∘
    centeredHalfDiskInclusion e hK

theorem contractedCenteredHalfDiskInclusion_coordinate {c β R : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * β) ↔ 0 ≤ w.im))
    (w : flatLinkSectorDisk Real.pi R) :
    sectorAngularMap c (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK w) =
      e w.1 := by
  have h := (closedSectorContractionHomeomorph hc hc1 hβ hβπ).apply_symm_apply
    (centeredHalfDiskInclusion e hK w)
  exact congrArg Subtype.val h

theorem contractedCenteredHalfDiskInclusion_continuous {c β R : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * β) ↔ 0 ≤ w.im)) :
    Continuous (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK) :=
  (closedSectorContractionHomeomorph hc hc1 hβ hβπ).symm.continuous.comp
    (centeredHalfDiskInclusion_isometry e hK).continuous

/-- The sharp comparison in actual old source distances. No new global
distance, path structure, or already-existing surgery chart is assumed. -/
theorem contractedCenteredHalfDiskInclusion_dist_bounds {c β R : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (e w ∈ closedEuclideanSector (c * β) ↔ 0 ≤ w.im))
    (x z : flatLinkSectorDisk Real.pi R) :
    c * dist (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK x)
      (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK z) ≤ dist x z ∧
      dist x z ≤ dist (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK x)
        (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK z) := by
  let E := closedSectorContractionHomeomorph hc hc1 hβ hβπ
  have h := closedSectorContractionEquiv_dist_bounds hc hc1 hβ hβπ
    (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK x)
    (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ e hK z)
  change c * dist (E.symm (centeredHalfDiskInclusion e hK x))
      (E.symm (centeredHalfDiskInclusion e hK z)) ≤
      dist (E (E.symm (centeredHalfDiskInclusion e hK x)))
        (E (E.symm (centeredHalfDiskInclusion e hK z))) ∧
      dist (E (E.symm (centeredHalfDiskInclusion e hK x)))
        (E (E.symm (centeredHalfDiskInclusion e hK z))) ≤
      dist (E.symm (centeredHalfDiskInclusion e hK x))
        (E.symm (centeredHalfDiskInclusion e hK z)) at h
  simpa only [E.apply_symm_apply, (centeredHalfDiskInclusion_isometry e hK).dist_eq,
    contractedCenteredHalfDiskInclusion, Function.comp_apply, E] using h

/-- On the whole diameter, both positive and negative arclength from the
passing point pull back to the original boundary line, without rescaling. -/
theorem contractedCenteredHalfDiskInclusion_seam {c β r R : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hRr : R < r) (top : Bool)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R →
      (sectorEdgeChart top r (c * β) w ∈ closedEuclideanSector (c * β) ↔ 0 ≤ w.im))
    (w : flatLinkSectorDisk Real.pi R) (hw : w.1.im = 0) :
    (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ
      (sectorEdgeChart top r (c * β)) hK w : ℂ) = sectorEdgeChart top r β w.1 := by
  have hreal : w.1 = (w.1.re : ℂ) := by
    apply Complex.ext <;> simp [hw]
  have hlow : -R ≤ w.1.re := by
    have hab : |w.1.re| ≤ R := (Complex.abs_re_le_norm w.1).trans w.2.2
    exact (abs_le.mp hab).1
  have hrt : 0 ≤ r + w.1.re := by linarith
  have hsource : sectorEdgeChart top r β w.1 ∈ closedEuclideanSector β := by
    rw [hreal, sectorEdgeChart_real]
    cases top
    · simpa using
        (flatLink_polar_mem_sector hβ hβπ hrt (0 : unitInterval))
    · simpa using
        (flatLink_polar_mem_sector hβ hβπ hrt (1 : unitInterval))
  let q : closedEuclideanSector β := ⟨sectorEdgeChart top r β w.1, hsource⟩
  have heq : contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ
      (sectorEdgeChart top r (c * β)) hK w = q := by
    apply (closedSectorContractionHomeomorph hc hc1 hβ hβπ).injective
    apply Subtype.ext
    change sectorAngularMap c (contractedCenteredHalfDiskInclusion hc hc1 hβ hβπ
      (sectorEdgeChart top r (c * β)) hK w) = sectorAngularMap c q.1
    rw [contractedCenteredHalfDiskInclusion_coordinate]
    change sectorEdgeChart top r (c * β) w.1 =
      sectorAngularMap c (sectorEdgeChart top r β w.1)
    rw [hreal, sectorAngularMap_sectorEdgeChart_real hβ hβπ hrt]
  exact congrArg Subtype.val heq

/-- Existence of the required post-contraction centered halfdisk, with
strictly positive radius. This is constructed from the literal target sector. -/
theorem exists_contractedPassingEdge_halfdisk {c β r : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hr : 0 < r) (top : Bool) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧ ∀ w : ℂ, ‖w‖ ≤ R →
      (sectorEdgeChart top r (c * β) w ∈ closedEuclideanSector (c * β) ↔
        0 ≤ w.im) := by
  exact exists_sectorEdge_centeredHalfDisk hr (mul_pos hc hβ)
    ((mul_le_of_le_one_left hβ.le hc1).trans hβπ) top

end RepulsiveCoulomb
