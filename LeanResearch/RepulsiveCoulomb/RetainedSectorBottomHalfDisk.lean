module

public import LeanResearch.RepulsiveCoulomb.PointRetainedApexInitialEntry
public import LeanResearch.RepulsiveCoulomb.RetainedSectorPassingHalfDisk

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. Literal source halfdisk at a positive-radius
bottom point, with exact source coverage. This is the local model needed to
prove that removing S\T is relatively open in the old halfplane. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def retainedSectorBottomHalfDisk {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β)
    (w : flatLinkSectorDisk Real.pi L) : closedEuclideanSector β := by
  have hw : 0 ≤ w.1.im ∧ ‖w.1‖ ≤ L :=
    ⟨Complex.arg_nonneg_iff.mp w.2.1.1, w.2.2⟩
  refine ⟨(r:ℂ)+w.1,?_⟩
  rcases lt_or_eq_of_le hβπ with hlt | heq
  · apply mem_closedEuclideanSector_of_halfplanes hβ hlt
    · simpa only [Complex.add_im,Complex.ofReal_im,zero_add] using hw.1
    · have hb : (conePhase (-β)*w.1).im ≤ L :=
        (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (by
          simpa only [norm_mul,conePhase_norm,one_mul] using hw.2))
      simp only [Complex.mul_im,conePhase_im,conePhase_re,Real.sin_neg,Real.cos_neg] at hb
      simp only [Complex.add_im,Complex.add_re,Complex.ofReal_im,Complex.ofReal_re,zero_add]
      nlinarith [hLsin hlt]
  · change 0 ≤ Complex.arg _ ∧ Complex.arg _ ≤ β
    refine ⟨Complex.arg_nonneg_iff.mpr ?_,?_⟩
    · simpa only [Complex.add_im,Complex.ofReal_im,zero_add] using hw.1
    · simpa only [heq] using Complex.arg_le_pi ((r:ℂ)+w.1)

@[simp] theorem retainedSectorBottomHalfDisk_apex {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    retainedSectorBottomHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL) =
      retainedApexBottomSource hβ.le hβπ ⟨r,hr⟩ := by
  apply Subtype.ext
  change (r : ℂ) + 0 = sectorPolar r 0
  simp [sectorPolar, conePhase]

theorem retainedSectorBottomHalfDisk_isometry {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) :
    Isometry (retainedSectorBottomHalfDisk hβ hβπ hLsin) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist ((r:ℂ)+z.1) ((r:ℂ)+w.1) = dist z.1 w.1
  exact dist_add_left _ _ _

/-- Every sufficiently close point of the source sector is in the literal
bottom halfdisk. No target-angle or old-region fullness assertion is assumed. -/
theorem retainedSectorBottomHalfDisk_local_coverage {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hr : 0 ≤ r)
    (z : closedEuclideanSector β)
    (hz : dist z (retainedApexBottomSource hβ.le hβπ ⟨r,hr⟩) ≤ L) :
    z ∈ range (retainedSectorBottomHalfDisk hβ hβπ hLsin) := by
  let w : ℂ := z.1-(r:ℂ)
  have hwim : 0 ≤ w.im := by
    simpa only [w,Complex.sub_im,Complex.ofReal_im,sub_zero] using
      (Complex.arg_nonneg_iff.mp z.2.1)
  have hwn : ‖w‖ ≤ L := by
    change dist z.1 (sectorPolar r 0) ≤ L at hz
    simpa only [w, dist_eq_norm, sectorPolar, conePhase, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one] using hz
  have hw : w ∈ flatLinkSectorDisk Real.pi L := by
    rw [flatLinkSectorDisk_pi]
    exact ⟨hwim,hwn⟩
  refine ⟨⟨w,hw⟩,Subtype.ext ?_⟩
  change (r:ℂ)+(z.1-(r:ℂ)) = z.1
  abel

/-- The two positive-radius real-edge points of the halfdisk lie on the
ACTUAL source bottom ray, provided the patch radius is less than its center. -/
theorem retainedSectorBottomHalfDisk_real_edge
    {β r L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hLr : L < r)
    (w : flatLinkSectorDisk Real.pi L) (hwim : w.1.im = 0) :
    ∃ u : NNReal, 0 < (u:ℝ) ∧ retainedSectorBottomHalfDisk hβ hβπ hLsin w =
      retainedApexBottomSource hβ.le hβπ u := by
  have hw : 0 ≤ w.1.im ∧ ‖w.1‖ ≤ L :=
    ⟨Complex.arg_nonneg_iff.mp w.2.1.1, w.2.2⟩
  have hp : 0 < r+w.1.re := by
    have ha := (Complex.abs_re_le_norm w.1).trans hw.2
    have hl := (abs_le.mp ha).1
    linarith
  refine ⟨⟨r+w.1.re,hp.le⟩,hp,Subtype.ext ?_⟩
  have hwreal : w.1 = (w.1.re:ℂ) := Complex.ext (by simp) (by simpa using hwim)
  change (r:ℂ)+w.1 = sectorPolar (r+w.1.re) 0
  rw [hwreal]
  simp [sectorPolar,conePhase]

/-- Global sector image and the bottom halfdisk have exactly the same local
germ, by all-pairs old-metric isometry and literal source coverage. -/
theorem pointRetainedSectorBottomHalfDisk_germ
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    {β r L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hr : 0 ≤ r)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {z : ℂ}
    (hz : (pointSmoothConformalEDist a y z
      (σ (retainedApexBottomSource hβ.le hβπ ⟨r,hr⟩))).toReal ≤ L) :
    z ∈ range σ ↔ z ∈ range (σ ∘ retainedSectorBottomHalfDisk hβ hβπ hLsin) := by
  constructor
  · rintro ⟨x,rfl⟩
    rw [hσ] at hz
    obtain ⟨w,hw⟩ := retainedSectorBottomHalfDisk_local_coverage hβ hβπ hLsin hr x hz
    exact ⟨w,congrArg σ hw⟩
  · rintro ⟨w,rfl⟩
    exact mem_range_self _

end RepulsiveCoulomb
