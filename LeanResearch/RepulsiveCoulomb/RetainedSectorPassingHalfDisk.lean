import LeanResearch.RepulsiveCoulomb.PointRetainedApexSectorGerms
import LeanResearch.RepulsiveCoulomb.EuclideanRetainedChord

/-!
SOURCE-ONLY, NOT COMPILED. The actual rigid halfdisk cut out of a supplied
Euclidean sector at a positive-radius point of its upper ray. This is a source
geometry construction; no target occupancy or complementary angle is assumed.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A source sector lies on the lower side of the supporting line of its
upper edge; the statement includes beta=pi. -/
theorem retainedSector_upper_halfplane {β : ℝ} (hβπ : β ≤ Real.pi)
    {z : ℂ} (hz : z ∈ closedEuclideanSector β) :
    Real.cos β*z.im-Real.sin β*z.re ≤ 0 := by
  have hangle : β-Complex.arg z ∈ Icc (0:ℝ) Real.pi :=
    ⟨sub_nonneg.mpr hz.2,by linarith [hz.1]⟩
  have hsin := Real.sin_nonneg_of_mem_Icc hangle
  have hid : Real.cos β*z.im-Real.sin β*z.re =
      -‖z‖*Real.sin (β-Complex.arg z) := by
    calc
      _ = (‖z‖*Real.sin (Complex.arg z))*Real.cos β-
          (‖z‖*Real.cos (Complex.arg z))*Real.sin β := by
            rw [Complex.norm_mul_sin_arg,Complex.norm_mul_cos_arg]
            ring
      _ = _ := by rw [Real.sin_sub]; ring
  rw [hid]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg z)) hsin

/-- Rigid inward halfdisk coordinates. The first coordinate ray points toward
the sector apex; the second points outward along the same upper edge. -/
def retainedSectorPassingPoint (β r : ℝ) (w : ℂ) : ℂ :=
  sectorPolar r β-conePhase β*w

theorem retainedSectorPassingPoint_upper_determinant (β r : ℝ) (w : ℂ) :
    Real.cos β*(retainedSectorPassingPoint β r w).im-
      Real.sin β*(retainedSectorPassingPoint β r w).re = -w.im := by
  simp only [retainedSectorPassingPoint,Complex.sub_im,Complex.sub_re,
    sectorPolar_im,sectorPolar_re,Complex.mul_im,Complex.mul_re,conePhase_im,conePhase_re]
  calc
    _ = -(Real.sin β^2+Real.cos β^2)*w.im := by ring
    _ = -w.im := by rw [Real.sin_sq_add_cos_sq]; ring

/-- The bounded source map is an actual isometric inclusion into the supplied
sector. For beta<pi, the radius avoids the opposite supporting boundary. -/
def retainedSectorPassingHalfDisk {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β)
    (w : flatLinkSectorDisk Real.pi L) : closedEuclideanSector β := by
  have hw : 0 ≤ w.1.im ∧ ‖w.1‖ ≤ L :=
    ⟨Complex.arg_nonneg_iff.mp w.2.1.1, w.2.2⟩
  refine ⟨retainedSectorPassingPoint β r w.1,?_⟩
  have hupper : Real.cos β*(retainedSectorPassingPoint β r w.1).im-
      Real.sin β*(retainedSectorPassingPoint β r w.1).re ≤ 0 := by
    rw [retainedSectorPassingPoint_upper_determinant]
    exact neg_nonpos.mpr hw.1
  rcases lt_or_eq_of_le hβπ with hlt | heq
  · apply mem_closedEuclideanSector_of_halfplanes hβ hlt _ hupper
    have hbound : (conePhase β*w.1).im ≤ L :=
      (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (by
        simpa only [norm_mul,conePhase_norm,one_mul] using hw.2))
    simp only [retainedSectorPassingPoint,Complex.sub_im,sectorPolar_im]
    linarith [hLsin hlt]
  · have him : (retainedSectorPassingPoint β r w.1).im = w.1.im := by
      simp only [heq,retainedSectorPassingPoint,Complex.sub_im,sectorPolar_im,
        Complex.mul_im,conePhase_re,conePhase_im,Real.sin_pi,Real.cos_pi]
      ring
    change 0 ≤ Complex.arg _ ∧ Complex.arg _ ≤ β
    refine ⟨Complex.arg_nonneg_iff.mpr (him.symm ▸ hw.1),?_⟩
    simpa only [heq] using Complex.arg_le_pi (retainedSectorPassingPoint β r w.1)

@[simp] theorem retainedSectorPassingHalfDisk_apex {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL) =
      retainedApexUpperSource hβ.le hβπ ⟨r,hr⟩ := by
  apply Subtype.ext
  change retainedSectorPassingPoint β r 0 = sectorPolar r β
  simp only [retainedSectorPassingPoint, mul_zero, sub_zero]

theorem retainedSectorPassingHalfDisk_isometry {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) :
    Isometry (retainedSectorPassingHalfDisk hβ hβπ hLsin) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist (retainedSectorPassingPoint β r z.1) (retainedSectorPassingPoint β r w.1) =
    dist z.1 w.1
  rw [dist_eq_norm,dist_eq_norm]
  have he : retainedSectorPassingPoint β r z.1-retainedSectorPassingPoint β r w.1 =
      -conePhase β*(z.1-w.1) := by unfold retainedSectorPassingPoint; ring
  rw [he,norm_mul,norm_neg,conePhase_norm,one_mul]

private theorem retainedSector_phase_mul_neg (β : ℝ) :
    conePhase β*conePhase (-β) = 1 := by
  unfold conePhase
  rw [← Complex.exp_add]
  have he : (β:ℂ)*Complex.I+((-β:ℝ):ℂ)*Complex.I = 0 := by push_cast; ring
  rw [he,Complex.exp_zero]

/-- Every source point close enough to the free edge belongs to the literal
halfdisk. This rules out missing source components in local occupancy. -/
theorem retainedSectorPassingHalfDisk_local_coverage {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hr : 0 ≤ r)
    (z : closedEuclideanSector β)
    (hz : dist z (retainedApexUpperSource hβ.le hβπ ⟨r,hr⟩) ≤ L) :
    z ∈ range (retainedSectorPassingHalfDisk hβ hβπ hLsin) := by
  let w : ℂ := conePhase (-β)*(sectorPolar r β-z.1)
  have hwim : 0 ≤ w.im := by
    have hzupper := retainedSector_upper_halfplane hβπ z.2
    dsimp [w]
    simp only [Complex.mul_im,Complex.sub_im,Complex.sub_re,sectorPolar_im,sectorPolar_re,
      conePhase_im,conePhase_re,Real.sin_neg,Real.cos_neg]
    nlinarith
  have hwn : ‖w‖ ≤ L := by
    dsimp [w]
    rw [norm_mul,conePhase_norm,one_mul, norm_sub_rev]
    change dist z.1 (sectorPolar r β) ≤ L at hz
    simpa only [dist_eq_norm] using hz
  have hw : w ∈ flatLinkSectorDisk Real.pi L := by
    rw [flatLinkSectorDisk_pi]
    exact ⟨hwim,hwn⟩
  refine ⟨⟨w,hw⟩,Subtype.ext ?_⟩
  change sectorPolar r β-conePhase β*(conePhase (-β)*(sectorPolar r β-z.1)) = z.1
  rw [← mul_assoc,retainedSector_phase_mul_neg,one_mul]
  abel

/-- A positive-radius upper point always admits a positive halfdisk radius.
The beta=pi case is included rather than lost through sin pi=0. -/
theorem retainedSectorPassingHalfDisk_exists_radius {β r : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 < r) :
    ∃ L : ℝ, 0 < L ∧ L < r ∧ (β < Real.pi → L ≤ r*Real.sin β) := by
  by_cases hlt : β < Real.pi
  · have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ hlt
    refine ⟨min r (r*Real.sin β)/2,half_pos (lt_min hr (mul_pos hr hs)),?_,?_⟩
    · have hm := min_le_left r (r*Real.sin β)
      linarith [lt_min hr (mul_pos hr hs)]
    · intro _
      have hm := min_le_right r (r*Real.sin β)
      linarith [lt_min hr (mul_pos hr hs)]
  · exact ⟨r/2,half_pos hr,half_lt_self hr,fun h ↦ False.elim (hlt h)⟩


/-- The local source straight edge is EXACTLY the global sector upper ray.
The positive-radius bound excludes the apex and the opposite continuation. -/
theorem retainedSectorPassingHalfDisk_mem_upper_iff {β r L : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hLr : L < r)
    (w : flatLinkSectorDisk Real.pi L) :
    retainedSectorPassingHalfDisk hβ hβπ hLsin w ∈
      range (retainedApexUpperSource hβ.le hβπ) ↔ w.1.im = 0 := by
  constructor
  · rintro ⟨u,hu⟩
    have he := congrArg (fun z : closedEuclideanSector β ↦
      Real.cos β*z.1.im-Real.sin β*z.1.re) hu
    change Real.cos β*(sectorPolar u β).im-Real.sin β*(sectorPolar u β).re =
      Real.cos β*(retainedSectorPassingPoint β r w.1).im-
        Real.sin β*(retainedSectorPassingPoint β r w.1).re at he
    rw [retainedSectorPassingPoint_upper_determinant,sectorPolar_im,sectorPolar_re] at he
    nlinarith
  · intro hw0
    have hw : 0 ≤ w.1.im ∧ ‖w.1‖ ≤ L :=
      ⟨Complex.arg_nonneg_iff.mp w.2.1.1, w.2.2⟩
    have hrw : 0 < r-w.1.re := by
      have hre := (le_abs_self w.1.re).trans (Complex.abs_re_le_norm w.1)
      linarith [hw.2]
    refine ⟨⟨r-w.1.re,hrw.le⟩,Subtype.ext ?_⟩
    change sectorPolar (r-w.1.re) β = sectorPolar r β-conePhase β*w.1
    have hwreal : w.1 = (w.1.re:ℂ) := Complex.ext (by simp) (by simpa using hw0)
    rw [hwreal]
    simp only [sectorPolar,Complex.ofReal_sub,Complex.ofReal_re]
    ring

/-- The actual global embedded sector and its actual passing halfdisk have
the same local image. All source points are covered using the global isometry. -/
theorem pointRetainedSectorPassingHalfDisk_germ
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    {β r L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (hLsin : β < Real.pi → L ≤ r*Real.sin β) (hr : 0 ≤ r)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {z : ℂ}
    (hz : (pointSmoothConformalEDist a y z
      (σ (retainedApexUpperSource hβ.le hβπ ⟨r,hr⟩))).toReal ≤ L) :
    z ∈ range σ ↔ z ∈ range (σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin) := by
  constructor
  · rintro ⟨x,rfl⟩
    rw [hσ] at hz
    obtain ⟨w,hw⟩ := retainedSectorPassingHalfDisk_local_coverage hβ hβπ hLsin hr x hz
    exact ⟨w,congrArg σ hw⟩
  · rintro ⟨w,rfl⟩
    exact mem_range_self _

end RepulsiveCoulomb
