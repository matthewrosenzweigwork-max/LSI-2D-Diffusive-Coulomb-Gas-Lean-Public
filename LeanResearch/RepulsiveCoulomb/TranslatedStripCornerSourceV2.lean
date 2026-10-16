module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripSourceGeometry
public import LeanResearch.RepulsiveCoulomb.FlatLinkSectorDisk
public import LeanResearch.RepulsiveCoulomb.EuclideanRetainedChord

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. The literal translated-strip corner at b*v
is a genuine bounded Euclidean sector of angle pi-lambda. Both inclusion and
full local source coverage are constructed, not assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The reverse of the existing short-sector halfplane test. -/
theorem closedEuclideanSector_halfplanes {β : ℝ} (hβπ : β ≤ Real.pi)
    {w : ℂ} (hw : w ∈ closedEuclideanSector β) :
    0 ≤ w.im ∧ Real.cos β*w.im-Real.sin β*w.re ≤ 0 := by
  have hs : 0 ≤ Real.sin (β-Complex.arg w) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hw.2) (by linarith [hw.1])
  have hid : Real.cos β*w.im-Real.sin β*w.re = -‖w‖*Real.sin (β-Complex.arg w) := by
    rw [Real.sin_sub,← Complex.norm_mul_sin_arg w,← Complex.norm_mul_cos_arg w]
    ring
  refine ⟨Complex.arg_nonneg_iff.mp hw.1,?_⟩
  rw [hid]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg w)) hs

/-- Rigid recentering: source angle zero is the compact edge directed back
from z, while source angle pi-lambda is the free top ray directed outward. -/
def translatedStripCornerRigid (stripAngle b : ℝ) (w : ℂ) : ℂ :=
  flatShearedPoint (conePhase stripAngle) 0 b-conePhase stripAngle*w

theorem translatedStripCornerRigid_isometry (stripAngle b : ℝ) :
    Isometry (translatedStripCornerRigid stripAngle b) := by
  apply Isometry.of_dist_eq
  intro w z
  rw [dist_eq_norm,dist_eq_norm]
  have he : translatedStripCornerRigid stripAngle b w-translatedStripCornerRigid stripAngle b z =
      conePhase stripAngle*(z-w) := by unfold translatedStripCornerRigid; ring
  rw [he,norm_mul,conePhase_norm,one_mul,norm_sub_rev]

@[simp] theorem translatedStripCornerRigid_zero (stripAngle b : ℝ) :
    translatedStripCornerRigid stripAngle b 0 = flatShearedPoint (conePhase stripAngle) 0 b := by
  simp [translatedStripCornerRigid]

/-- Literal strip coordinates of the rotated source corner. -/
theorem translatedStripCornerRigid_coordinates {stripAngle b : ℝ} (hs : Real.sin stripAngle ≠ 0) (w : ℂ) :
    translatedStripCornerRigid stripAngle b w = flatShearedPoint (conePhase stripAngle)
      (w.im/Real.sin stripAngle) (b-(conePhase stripAngle*w).im/Real.sin stripAngle) := by
  apply Complex.ext
  · simp only [translatedStripCornerRigid,flatShearedPoint,Complex.sub_re,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,zero_add,conePhase_re,conePhase_im]
    field_simp [hs]
    have hu := congrArg (fun x : ℝ ↦ w.im*x) (Real.sin_sq_add_cos_sq stripAngle)
    nlinarith [hu]
  · simp only [translatedStripCornerRigid,flatShearedPoint,Complex.sub_im,Complex.add_im,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,
      zero_add,conePhase_re,conePhase_im]
    field_simp [hs]
    ring

theorem translatedStripCornerRigid_mem {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b*Real.sin stripAngle)
    {w : ℂ} (hw : w ∈ flatLinkSectorDisk (Real.pi-stripAngle) L) :
    translatedStripCornerRigid stripAngle b w ∈ flatShearedStrip (conePhase stripAngle) b := by
  have hs : 0 < Real.sin stripAngle := Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  have hβπ : Real.pi-stripAngle ≤ Real.pi := by linarith
  obtain ⟨hwim,hhalf⟩ := closedEuclideanSector_halfplanes hβπ hw.1
  have hD : 0 ≤ (conePhase stripAngle*w).im := by
    rw [Real.cos_pi_sub,Real.sin_pi_sub] at hhalf
    simp only [Complex.mul_im,conePhase_re,conePhase_im]
    nlinarith [hhalf]
  have hDle : (conePhase stripAngle*w).im ≤ b*Real.sin stripAngle := by
    have hn : ‖conePhase stripAngle*w‖ = ‖w‖ := by rw [norm_mul,conePhase_norm,one_mul]
    exact (Complex.im_le_norm _).trans (hn.trans_le (hw.2.trans hL))
  have hu0 : 0 ≤ b-(conePhase stripAngle*w).im/Real.sin stripAngle :=
    sub_nonneg.mpr ((div_le_iff₀ hs).mpr hDle)
  have hub : b-(conePhase stripAngle*w).im/Real.sin stripAngle ≤ b :=
    sub_le_self _ (div_nonneg hD hs.le)
  exact ⟨w.im/Real.sin stripAngle,div_nonneg hwim hs.le,
    b-(conePhase stripAngle*w).im/Real.sin stripAngle,⟨hu0,hub⟩,translatedStripCornerRigid_coordinates hs.ne' w⟩

/-- The actual bounded corner map into the literal strip. -/
def translatedStripCornerSource {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b*Real.sin stripAngle) :
    flatLinkSectorDisk (Real.pi-stripAngle) L → flatShearedStrip (conePhase stripAngle) b := fun w ↦
  ⟨translatedStripCornerRigid stripAngle b w.1,translatedStripCornerRigid_mem stripAngle_pos stripAngle_lt_pi hL w.2⟩

theorem translatedStripCornerSource_isometry {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b*Real.sin stripAngle) :
    Isometry (translatedStripCornerSource stripAngle_pos stripAngle_lt_pi hL) := by
  apply Isometry.of_dist_eq
  intro w z
  exact (translatedStripCornerRigid_isometry stripAngle b).dist_eq w.1 z.1

/-- Exact inverse source coordinates, including the compact edge and free ray. -/
theorem translatedStripCornerRigid_inverse (stripAngle b r u : ℝ) :
    translatedStripCornerRigid stripAngle b
      (((b-u : ℝ) : ℂ)-(r : ℂ)*starRingEnd ℂ (conePhase stripAngle)) =
        flatShearedPoint (conePhase stripAngle) r u := by
  have hv : conePhase stripAngle*starRingEnd ℂ (conePhase stripAngle) = 1 := by
    rw [Complex.mul_conj',conePhase_norm]
    norm_num
  unfold translatedStripCornerRigid flatShearedPoint
  push_cast
  calc
    _ = (u : ℂ)*conePhase stripAngle+(r : ℂ)*(conePhase stripAngle*starRingEnd ℂ (conePhase stripAngle)) := by ring
    _ = _ := by rw [hv]; ring

/-- The inverse of every actual strip point lies in the correct full source
sector. This is not just a local tangent-angle statement. -/
theorem translatedStripCorner_inverse_mem_sector {stripAngle b r u : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hr : 0 ≤ r) (hub : u ≤ b) :
    (((b-u : ℝ) : ℂ)-(r : ℂ)*starRingEnd ℂ (conePhase stripAngle)) ∈
      closedEuclideanSector (Real.pi-stripAngle) := by
  have hs : 0 ≤ Real.sin stripAngle := (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).le
  apply mem_closedEuclideanSector_of_halfplanes (by linarith) (by linarith)
  · simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.conj_im,conePhase_im,zero_mul,zero_add]
    nlinarith [mul_nonneg hr hs]
  · simp only [Complex.sub_im,Complex.sub_re,Complex.ofReal_im,Complex.ofReal_re,
      Complex.mul_im,Complex.mul_re,Complex.conj_im,Complex.conj_re,
      conePhase_im,conePhase_re,zero_mul,mul_zero,zero_add,sub_zero,
      Real.cos_pi_sub,Real.sin_pi_sub]
    nlinarith [mul_nonneg (sub_nonneg.mpr hub) hs]

/-- Full local coverage of the source strip, including both rays and z.
The radius condition excludes the opposite bottom edge; no target geometry
or residual certificate is involved. -/
theorem translatedStripCornerSource_local_coverage {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 ≤ b)
    (hL : L ≤ b*Real.sin stripAngle) (q : flatShearedStrip (conePhase stripAngle) b)
    (hq : dist q (translatedStripTop hb 0) ≤ L) :
    q ∈ range (translatedStripCornerSource stripAngle_pos stripAngle_lt_pi hL) := by
  obtain ⟨r,hr,u,hu,hqu⟩ := q.2
  let w : ℂ := ((b-u : ℝ) : ℂ)-(r : ℂ)*starRingEnd ℂ (conePhase stripAngle)
  have hsector : w ∈ closedEuclideanSector (Real.pi-stripAngle) :=
    translatedStripCorner_inverse_mem_sector stripAngle_pos stripAngle_lt_pi hr hu.2
  have hmap : translatedStripCornerRigid stripAngle b w = q.1 := by
    rw [translatedStripCornerRigid_inverse]
    exact hqu.symm
  have hwnorm : ‖w‖ ≤ L := by
    have he := (translatedStripCornerRigid_isometry stripAngle b).dist_eq w 0
    rw [hmap,translatedStripCornerRigid_zero,dist_zero_right] at he
    change dist q.1 (flatShearedPoint (conePhase stripAngle) 0 b) ≤ L at hq
    exact he.symm.trans_le hq
  refine ⟨⟨w,hsector,hwnorm⟩,Subtype.ext ?_⟩
  exact hmap

/-- The bounded corner image is exactly the strip's Euclidean closed-ball
intersection at its upper-left corner. This upgrades one-way coverage to an
actual source-image identity. -/
theorem translatedStripCornerSource_range {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 ≤ b)
    (hL : L ≤ b * Real.sin stripAngle) :
    range (translatedStripCornerSource stripAngle_pos stripAngle_lt_pi hL) =
      closedBall (translatedStripTop hb 0) L := by
  ext q
  constructor
  · rintro ⟨w, rfl⟩
    change dist (translatedStripCornerRigid stripAngle b w.1)
      (flatShearedPoint (conePhase stripAngle) 0 b) ≤ L
    rw [← translatedStripCornerRigid_zero stripAngle b,
      (translatedStripCornerRigid_isometry stripAngle b).dist_eq, dist_zero_right]
    exact w.2.2
  · intro hq
    exact translatedStripCornerSource_local_coverage stripAngle_pos stripAngle_lt_pi hb hL q hq

/-- Ambient form of the exact upper-left local-source identity. -/
theorem translatedStripCornerRigid_image {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 ≤ b)
    (hL : L ≤ b * Real.sin stripAngle) :
    translatedStripCornerRigid stripAngle b '' flatLinkSectorDisk (Real.pi - stripAngle) L =
      flatShearedStrip (conePhase stripAngle) b ∩
        closedBall (flatShearedPoint (conePhase stripAngle) 0 b) L := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨translatedStripCornerRigid_mem stripAngle_pos stripAngle_lt_pi hL hw, ?_⟩
    change dist (translatedStripCornerRigid stripAngle b w)
      (flatShearedPoint (conePhase stripAngle) 0 b) ≤ L
    rw [← translatedStripCornerRigid_zero stripAngle b,
      (translatedStripCornerRigid_isometry stripAngle b).dist_eq, dist_zero_right]
    exact hw.2
  · rintro ⟨hz, hzL⟩
    obtain ⟨w, hw⟩ := translatedStripCornerSource_local_coverage
      stripAngle_pos stripAngle_lt_pi hb hL ⟨z, hz⟩ hzL
    exact ⟨w.1, w.2, congrArg Subtype.val hw⟩

/-- Angle zero follows the compact edge back from the upper-left corner. -/
@[simp] theorem translatedStripCornerRigid_edge_zero (stripAngle b r : ℝ) :
    translatedStripCornerRigid stripAngle b (sectorPolar r 0) =
      flatShearedPoint (conePhase stripAngle) 0 (b - r) := by
  simp only [translatedStripCornerRigid, flatShearedPoint, sectorPolar,
    conePhase, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    zero_add, Complex.ofReal_sub]
  ring

/-- The opposite edge follows the free top ray in its positive-time direction. -/
@[simp] theorem translatedStripCornerRigid_edge_aperture (stripAngle b r : ℝ) :
    translatedStripCornerRigid stripAngle b (sectorPolar r (Real.pi - stripAngle)) =
      flatShearedPoint (conePhase stripAngle) r b := by
  have hp : conePhase stripAngle * conePhase (Real.pi - stripAngle) = -1 := by
    apply Complex.ext
    · simp only [Complex.mul_re, conePhase_re, conePhase_im,
        Real.cos_pi_sub, Real.sin_pi_sub, Complex.neg_re, Complex.one_re]
      nlinarith [Real.sin_sq_add_cos_sq stripAngle]
    · simp only [Complex.mul_im, conePhase_re, conePhase_im,
        Real.cos_pi_sub, Real.sin_pi_sub, Complex.neg_im, Complex.one_im]
      ring
  unfold translatedStripCornerRigid flatShearedPoint sectorPolar
  calc
    _ = (b : ℂ) * conePhase stripAngle -
        (r : ℂ) * (conePhase stripAngle * conePhase (Real.pi - stripAngle)) := by
      simp only [Complex.ofReal_zero, zero_add]
      ring
    _ = _ := by rw [hp]; ring

/-- A strictly positive admissible radius is available without an additional
local-coverage hypothesis. -/
theorem translatedStripCorner_radius {stripAngle b : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 < b) :
    0 < b * Real.sin stripAngle / 2 ∧
      b * Real.sin stripAngle / 2 ≤ b * Real.sin stripAngle := by
  have hp := mul_pos hb (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi)
  exact ⟨half_pos hp, (half_lt_self hp).le⟩

end RepulsiveCoulomb
