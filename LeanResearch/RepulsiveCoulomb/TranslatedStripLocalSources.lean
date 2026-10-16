import LeanResearch.RepulsiveCoulomb.TranslatedStripCornerSourceV2

/-! NEW SOURCE-ONLY, UNCOMPILED. Literal Euclidean local models for all
remaining translated-strip boundary strata. Every model has exact ambient
image equality, and each small-radius hypothesis has a concrete positive
choice. No residual topology or target-cone coverage is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Signed inward distance from the supporting compact-edge line. -/
def translatedStripInward (stripAngle : ℝ) (z : ℂ) : ℝ :=
  Real.sin stripAngle * z.re - Real.cos stripAngle * z.im

theorem translatedStripInward_abs_le (stripAngle : ℝ) (z : ℂ) :
    |translatedStripInward stripAngle z| ≤ ‖z‖ := by
  have he : translatedStripInward stripAngle z =
      -(starRingEnd ℂ (conePhase stripAngle) * z).im := by
    simp only [translatedStripInward, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, conePhase_re, conePhase_im]
    ring
  rw [he, abs_neg]
  calc
    _ ≤ ‖starRingEnd ℂ (conePhase stripAngle) * z‖ := Complex.abs_im_le_norm _
    _ = ‖z‖ := by rw [norm_mul, Complex.norm_conj, conePhase_norm, one_mul]

@[simp] theorem translatedStripInward_sheared (stripAngle r u : ℝ) :
    translatedStripInward stripAngle (flatShearedPoint (conePhase stripAngle) r u) =
      r * Real.sin stripAngle := by
  simp only [translatedStripInward, flatShearedPoint, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, conePhase_re, conePhase_im]
  ring

@[simp] theorem translatedStripInward_add (stripAngle : ℝ) (z w : ℂ) :
    translatedStripInward stripAngle (z + w) =
      translatedStripInward stripAngle z + translatedStripInward stripAngle w := by
  simp only [translatedStripInward, Complex.add_re, Complex.add_im]
  ring

@[simp] theorem translatedStripInward_sub (stripAngle : ℝ) (z w : ℂ) :
    translatedStripInward stripAngle (z - w) =
      translatedStripInward stripAngle z - translatedStripInward stripAngle w := by
  simp only [translatedStripInward, Complex.sub_re, Complex.sub_im]
  ring

/-- Three supporting halfplanes characterize the actual sheared strip. -/
theorem mem_flatShearedStrip_iff_halfplanes {stripAngle b : ℝ}
    (hs : 0 < Real.sin stripAngle) {z : ℂ} :
    z ∈ flatShearedStrip (conePhase stripAngle) b ↔
      0 ≤ z.im ∧ z.im ≤ b * Real.sin stripAngle ∧ 0 ≤ translatedStripInward stripAngle z := by
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    have hi : (flatShearedPoint (conePhase stripAngle) r u).im = u * Real.sin stripAngle := by
      simp [flatShearedPoint, conePhase_im]
    rw [hi, translatedStripInward_sheared]
    exact ⟨mul_nonneg hu.1 hs.le, mul_le_mul_of_nonneg_right hu.2 hs.le,
      mul_nonneg hr hs.le⟩
  · rintro ⟨hi, hib, hside⟩
    refine ⟨translatedStripInward stripAngle z / Real.sin stripAngle, div_nonneg hside hs.le,
      z.im / Real.sin stripAngle, ⟨div_nonneg hi hs.le, (div_le_iff₀ hs).mpr hib⟩, ?_⟩
    apply Complex.ext
    · simp only [flatShearedPoint, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, conePhase_re, mul_zero, sub_zero,
        translatedStripInward]
      field_simp [hs.ne'] <;> ring
    · simp only [flatShearedPoint, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, conePhase_im, zero_mul, zero_add, add_zero]
      exact (div_mul_cancel₀ _ hs.ne').symm

/-- The actual old lower-left corner is a full bounded sector of angle λ. -/
theorem translatedStripBottomCorner_image {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b * Real.sin stripAngle) :
    flatLinkSectorDisk stripAngle L =
      flatShearedStrip (conePhase stripAngle) b ∩ closedBall (0 : ℂ) L := by
  have hs := Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  ext z
  constructor
  · rintro ⟨hz, hzL⟩
    obtain ⟨hi, hw⟩ := closedEuclideanSector_halfplanes stripAngle_lt_pi.le hz
    refine ⟨(mem_flatShearedStrip_iff_halfplanes hs).mpr
      ⟨hi, (Complex.im_le_norm z).trans (hzL.trans hL), ?_⟩, ?_⟩
    · dsimp [translatedStripInward]
      linarith
    · simpa only [mem_closedBall, dist_zero_right, mem_setOf_eq] using hzL
  · rintro ⟨hz, hzL⟩
    obtain ⟨hi, _, hw⟩ := (mem_flatShearedStrip_iff_halfplanes hs).mp hz
    refine ⟨mem_closedEuclideanSector_of_halfplanes stripAngle_pos stripAngle_lt_pi hi ?_, ?_⟩
    · dsimp [translatedStripInward] at hw
      linarith
    · simpa only [mem_closedBall, dist_zero_right, mem_setOf_eq] using hzL

/-- Top-edge upper-halfdisk source: angle zero runs backward along the top,
and angle pi runs forward. -/
def translatedStripTopRigid (stripAngle b t : ℝ) (w : ℂ) : ℂ :=
  flatShearedPoint (conePhase stripAngle) t b - w

theorem translatedStripTopRigid_isometry (stripAngle b t : ℝ) :
    Isometry (translatedStripTopRigid stripAngle b t) := by
  apply Isometry.of_dist_eq
  intro w z
  simp only [translatedStripTopRigid, dist_eq_norm]
  have he : flatShearedPoint (conePhase stripAngle) t b - w -
      (flatShearedPoint (conePhase stripAngle) t b - z) = z - w := by ring
  rw [he, norm_sub_rev]

@[simp] theorem translatedStripTopRigid_zero (stripAngle b t : ℝ) :
    translatedStripTopRigid stripAngle b t 0 = flatShearedPoint (conePhase stripAngle) t b := by
  simp [translatedStripTopRigid]

theorem translatedStripTopRigid_mem {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) {w : ℂ}
    (hw : w ∈ flatLinkSectorDisk Real.pi L) :
    translatedStripTopRigid stripAngle b t w ∈ flatShearedStrip (conePhase stripAngle) b := by
  rw [flatLinkSectorDisk_pi] at hw
  have him : (translatedStripTopRigid stripAngle b t w).im = b * Real.sin stripAngle - w.im := by
    simp [translatedStripTopRigid, flatShearedPoint, conePhase_im]
  have hside : translatedStripInward stripAngle (translatedStripTopRigid stripAngle b t w) =
      t * Real.sin stripAngle - translatedStripInward stripAngle w := by
    simp only [translatedStripTopRigid, translatedStripInward_sub,
      translatedStripInward_sheared]
  have hiL := (Complex.im_le_norm w).trans hw.2
  have hsL := (abs_le.mp (translatedStripInward_abs_le stripAngle w)).2.trans hw.2
  apply (mem_flatShearedStrip_iff_halfplanes hs).mpr
  rw [him, hside]
  exact ⟨by linarith, by linarith [hw.1], by linarith⟩

/-- Exact local top-edge halfdisk coverage, including the whole diameter. -/
theorem translatedStripTopRigid_image {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) :
    translatedStripTopRigid stripAngle b t '' flatLinkSectorDisk Real.pi L =
      flatShearedStrip (conePhase stripAngle) b ∩
        closedBall (flatShearedPoint (conePhase stripAngle) t b) L := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨translatedStripTopRigid_mem hs hLb hLt hw, ?_⟩
    change dist (translatedStripTopRigid stripAngle b t w)
      (flatShearedPoint (conePhase stripAngle) t b) ≤ L
    rw [← translatedStripTopRigid_zero stripAngle b t,
      (translatedStripTopRigid_isometry stripAngle b t).dist_eq, dist_zero_right]
    exact hw.2
  · rintro ⟨hz, hzL⟩
    let w := flatShearedPoint (conePhase stripAngle) t b - z
    have hwi : 0 ≤ w.im := by
      obtain ⟨_, hi, _⟩ := (mem_flatShearedStrip_iff_halfplanes hs).mp hz
      dsimp [w]
      simp only [Complex.sub_im, flatShearedPoint, Complex.add_im,
        Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        conePhase_im, zero_mul, zero_add]
      linarith
    have hwL : ‖w‖ ≤ L := by
      simpa only [w, mem_closedBall, dist_eq_norm, norm_sub_rev] using hzL
    refine ⟨w, ?_, ?_⟩
    · rw [flatLinkSectorDisk_pi]
      exact ⟨hwi, hwL⟩
    · dsimp [translatedStripTopRigid, w]
      ring

/-- Bottom-edge upper-halfdisk source, centered at positive time t. -/
def translatedStripBottomRigid (t : ℝ) (w : ℂ) : ℂ := (t : ℂ) + w

theorem translatedStripBottomRigid_isometry (t : ℝ) :
    Isometry (translatedStripBottomRigid t) := by
  apply Isometry.of_dist_eq
  intro w z
  simp only [translatedStripBottomRigid, dist_add_left]

@[simp] theorem translatedStripBottomRigid_zero (t : ℝ) :
    translatedStripBottomRigid t 0 = (t : ℂ) := by simp [translatedStripBottomRigid]

theorem translatedStripBottomRigid_mem {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) {w : ℂ}
    (hw : w ∈ flatLinkSectorDisk Real.pi L) :
    translatedStripBottomRigid t w ∈ flatShearedStrip (conePhase stripAngle) b := by
  rw [flatLinkSectorDisk_pi] at hw
  have hi : (translatedStripBottomRigid t w).im = w.im := by
    simp [translatedStripBottomRigid]
  have hside : translatedStripInward stripAngle (translatedStripBottomRigid t w) =
      t * Real.sin stripAngle + translatedStripInward stripAngle w := by
    simp only [translatedStripBottomRigid, translatedStripInward,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsL := (abs_le.mp (translatedStripInward_abs_le stripAngle w)).1
  apply (mem_flatShearedStrip_iff_halfplanes hs).mpr
  rw [hi, hside]
  exact ⟨hw.1, (Complex.im_le_norm w).trans (hw.2.trans hLb), by linarith [hw.2]⟩

/-- Exact local bottom-edge halfdisk coverage. -/
theorem translatedStripBottomRigid_image {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) :
    translatedStripBottomRigid t '' flatLinkSectorDisk Real.pi L =
      flatShearedStrip (conePhase stripAngle) b ∩ closedBall (t : ℂ) L := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨translatedStripBottomRigid_mem hs hLb hLt hw, ?_⟩
    change dist (translatedStripBottomRigid t w) (t : ℂ) ≤ L
    rw [← translatedStripBottomRigid_zero t,
      (translatedStripBottomRigid_isometry t).dist_eq, dist_zero_right]
    exact hw.2
  · rintro ⟨hz, hzL⟩
    let w := z - (t : ℂ)
    have hwi : 0 ≤ w.im := by
      have hi := ((mem_flatShearedStrip_iff_halfplanes hs).mp hz).1
      simpa only [w, Complex.sub_im, Complex.ofReal_im, sub_zero] using hi
    have hwL : ‖w‖ ≤ L := by
      simpa only [w, mem_closedBall, dist_eq_norm] using hzL
    refine ⟨w, ?_, ?_⟩
    · rw [flatLinkSectorDisk_pi]
      exact ⟨hwi, hwL⟩
    · dsimp [translatedStripBottomRigid, w]
      ring

/-- Both open horizontal edges admit this concrete strictly positive radius. -/
theorem translatedStripHorizontal_radius {stripAngle b t : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 < b) (ht : 0 < t) :
    0 < min b t * Real.sin stripAngle / 2 ∧
      min b t * Real.sin stripAngle / 2 ≤ b * Real.sin stripAngle ∧
      min b t * Real.sin stripAngle / 2 ≤ t * Real.sin stripAngle := by
  have hs := Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  have hp : 0 < min b t * Real.sin stripAngle := mul_pos (lt_min hb ht) hs
  have hh := (half_lt_self hp).le
  exact ⟨half_pos hp, hh.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le),
    hh.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le)⟩

/-- At an interior compact-edge point, the existing corner rigid map with
center u*v parametrizes the complete inward halfdisk. -/
theorem translatedStripEdgeRigid_mem {stripAngle b u L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLu : L ≤ u * Real.sin stripAngle)
    (hLbu : L ≤ (b - u) * Real.sin stripAngle) {w : ℂ}
    (hw : w ∈ flatLinkSectorDisk Real.pi L) :
    translatedStripCornerRigid stripAngle u w ∈ flatShearedStrip (conePhase stripAngle) b := by
  rw [flatLinkSectorDisk_pi] at hw
  have hp : ‖conePhase stripAngle * w‖ = ‖w‖ := by
    rw [norm_mul, conePhase_norm, one_mul]
  have himabs : |(conePhase stripAngle * w).im| ≤ L :=
    (Complex.abs_im_le_norm _).trans (hp.trans_le hw.2)
  have him : (translatedStripCornerRigid stripAngle u w).im =
      u * Real.sin stripAngle - (conePhase stripAngle * w).im := by
    simp [translatedStripCornerRigid, flatShearedPoint, conePhase_im]
  have hside : translatedStripInward stripAngle (translatedStripCornerRigid stripAngle u w) = w.im := by
    simp only [translatedStripInward, translatedStripCornerRigid, flatShearedPoint,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      conePhase_re, conePhase_im]
    have hu := congrArg (fun x : ℝ ↦ w.im * x) (Real.sin_sq_add_cos_sq stripAngle)
    nlinarith [hu]
  apply (mem_flatShearedStrip_iff_halfplanes hs).mpr
  rw [him, hside]
  obtain ⟨hlo, hhi⟩ := abs_le.mp himabs
  exact ⟨by linarith, by nlinarith, hw.1⟩

/-- Exact local compact-edge halfdisk coverage with no omitted component. -/
theorem translatedStripEdgeRigid_image {stripAngle b u L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLu : L ≤ u * Real.sin stripAngle)
    (hLbu : L ≤ (b - u) * Real.sin stripAngle) :
    translatedStripCornerRigid stripAngle u '' flatLinkSectorDisk Real.pi L =
      flatShearedStrip (conePhase stripAngle) b ∩
        closedBall (flatShearedPoint (conePhase stripAngle) 0 u) L := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨translatedStripEdgeRigid_mem hs hLu hLbu hw, ?_⟩
    change dist (translatedStripCornerRigid stripAngle u w)
      (flatShearedPoint (conePhase stripAngle) 0 u) ≤ L
    rw [← translatedStripCornerRigid_zero stripAngle u,
      (translatedStripCornerRigid_isometry stripAngle u).dist_eq, dist_zero_right]
    exact hw.2
  · rintro ⟨⟨r, hr, q, hq, hz⟩, hzL⟩
    let w : ℂ := ((u - q : ℝ) : ℂ) - (r : ℂ) * starRingEnd ℂ (conePhase stripAngle)
    have hmap : translatedStripCornerRigid stripAngle u w = z := by
      rw [translatedStripCornerRigid_inverse]
      exact hz.symm
    have hwi : 0 ≤ w.im := by
      dsimp [w]
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.conj_im, conePhase_im, zero_mul, zero_add]
      nlinarith [mul_nonneg hr hs.le]
    have hwL : ‖w‖ ≤ L := by
      have he := (translatedStripCornerRigid_isometry stripAngle u).dist_eq w 0
      rw [hmap, translatedStripCornerRigid_zero, dist_zero_right] at he
      exact he.symm.trans_le hzL
    refine ⟨w, ?_, hmap⟩
    rw [flatLinkSectorDisk_pi]
    exact ⟨hwi, hwL⟩

/-- Every point strictly between the two compact-edge corners has a concrete
strictly positive admissible halfdisk radius. -/
theorem translatedStripEdge_radius {stripAngle b u : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hu : 0 < u) (hub : u < b) :
    0 < min u (b - u) * Real.sin stripAngle / 2 ∧
      min u (b - u) * Real.sin stripAngle / 2 ≤ u * Real.sin stripAngle ∧
      min u (b - u) * Real.sin stripAngle / 2 ≤ (b - u) * Real.sin stripAngle := by
  have hs := Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  have hp : 0 < min u (b - u) * Real.sin stripAngle :=
    mul_pos (lt_min hu (sub_pos.mpr hub)) hs
  have hh := (half_lt_self hp).le
  exact ⟨half_pos hp, hh.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le),
    hh.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le)⟩

/-- Top halfdisk with the literal source-strip codomain required by an
actual translated-strip embedding. -/
def translatedStripTopSource {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) :
    flatLinkSectorDisk Real.pi L → flatShearedStrip (conePhase stripAngle) b := fun w ↦
  ⟨translatedStripTopRigid stripAngle b t w.1, translatedStripTopRigid_mem hs hLb hLt w.2⟩

theorem translatedStripTopSource_isometry {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) :
    Isometry (translatedStripTopSource hs hLb hLt) := by
  apply Isometry.of_dist_eq
  intro w z
  exact (translatedStripTopRigid_isometry stripAngle b t).dist_eq w.1 z.1

def translatedStripBottomSource {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) :
    flatLinkSectorDisk Real.pi L → flatShearedStrip (conePhase stripAngle) b := fun w ↦
  ⟨translatedStripBottomRigid t w.1, translatedStripBottomRigid_mem hs hLb hLt w.2⟩

theorem translatedStripBottomSource_isometry {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) :
    Isometry (translatedStripBottomSource hs hLb hLt) := by
  apply Isometry.of_dist_eq
  intro w z
  exact (translatedStripBottomRigid_isometry t).dist_eq w.1 z.1

def translatedStripEdgeSource {stripAngle b u L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLu : L ≤ u * Real.sin stripAngle)
    (hLbu : L ≤ (b - u) * Real.sin stripAngle) :
    flatLinkSectorDisk Real.pi L → flatShearedStrip (conePhase stripAngle) b := fun w ↦
  ⟨translatedStripCornerRigid stripAngle u w.1, translatedStripEdgeRigid_mem hs hLu hLbu w.2⟩

theorem translatedStripEdgeSource_isometry {stripAngle b u L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLu : L ≤ u * Real.sin stripAngle)
    (hLbu : L ≤ (b - u) * Real.sin stripAngle) :
    Isometry (translatedStripEdgeSource hs hLu hLbu) := by
  apply Isometry.of_dist_eq
  intro w z
  exact (translatedStripCornerRigid_isometry stripAngle u).dist_eq w.1 z.1

/-- The closed halfdisk's two boundary rays are the signed real axes. -/
@[simp] theorem translatedStrip_sectorPolar_zero_angle (r : ℝ) :
    sectorPolar r 0 = (r : ℂ) := by
  simp [sectorPolar, conePhase]

@[simp] theorem translatedStrip_sectorPolar_pi (r : ℝ) :
    sectorPolar r Real.pi = -(r : ℂ) := by
  apply Complex.ext <;> simp [sectorPolar_re, sectorPolar_im]

@[simp] theorem translatedStripTopRigid_edge_zero (stripAngle b t r : ℝ) :
    translatedStripTopRigid stripAngle b t (sectorPolar r 0) =
      flatShearedPoint (conePhase stripAngle) (t - r) b := by
  simp only [translatedStrip_sectorPolar_zero_angle, translatedStripTopRigid,
    flatShearedPoint, Complex.ofReal_sub]
  ring

@[simp] theorem translatedStripTopRigid_edge_pi (stripAngle b t r : ℝ) :
    translatedStripTopRigid stripAngle b t (sectorPolar r Real.pi) =
      flatShearedPoint (conePhase stripAngle) (t + r) b := by
  simp only [translatedStrip_sectorPolar_pi, translatedStripTopRigid,
    flatShearedPoint, Complex.ofReal_add]
  ring

@[simp] theorem translatedStripBottomRigid_edge_zero (t r : ℝ) :
    translatedStripBottomRigid t (sectorPolar r 0) = ((t + r : ℝ) : ℂ) := by
  simp [translatedStripBottomRigid]

@[simp] theorem translatedStripBottomRigid_edge_pi (t r : ℝ) :
    translatedStripBottomRigid t (sectorPolar r Real.pi) = ((t - r : ℝ) : ℂ) := by
  simp [translatedStripBottomRigid, sub_eq_add_neg]

@[simp] theorem translatedStripEdgeRigid_edge_pi (stripAngle u r : ℝ) :
    translatedStripCornerRigid stripAngle u (sectorPolar r Real.pi) =
      flatShearedPoint (conePhase stripAngle) 0 (u + r) := by
  simp only [translatedStrip_sectorPolar_pi, translatedStripCornerRigid,
    flatShearedPoint, Complex.ofReal_add, zero_add]
  ring

/-- The lower-left sector's two edge maps are the old bottom and compact edge. -/
@[simp] theorem translatedStripBottomCorner_edge_aperture (stripAngle r : ℝ) :
    sectorPolar r stripAngle = flatShearedPoint (conePhase stripAngle) 0 r := by
  simp [sectorPolar, flatShearedPoint]

theorem translatedStripTopSource_local_coverage {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) (q : flatShearedStrip (conePhase stripAngle) b)
    (hq : dist q.1 (flatShearedPoint (conePhase stripAngle) t b) ≤ L) :
    q ∈ range (translatedStripTopSource hs hLb hLt) := by
  have hi : q.1 ∈ translatedStripTopRigid stripAngle b t '' flatLinkSectorDisk Real.pi L := by
    rw [translatedStripTopRigid_image hs hLb hLt]
    exact ⟨q.2, hq⟩
  obtain ⟨w, hw, he⟩ := hi
  exact ⟨⟨w, hw⟩, Subtype.ext he⟩

theorem translatedStripBottomSource_local_coverage {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLb : L ≤ b * Real.sin stripAngle)
    (hLt : L ≤ t * Real.sin stripAngle) (q : flatShearedStrip (conePhase stripAngle) b)
    (hq : dist q.1 (t : ℂ) ≤ L) :
    q ∈ range (translatedStripBottomSource hs hLb hLt) := by
  have hi : q.1 ∈ translatedStripBottomRigid t '' flatLinkSectorDisk Real.pi L := by
    rw [translatedStripBottomRigid_image hs hLb hLt]
    exact ⟨q.2, hq⟩
  obtain ⟨w, hw, he⟩ := hi
  exact ⟨⟨w, hw⟩, Subtype.ext he⟩

theorem translatedStripEdgeSource_local_coverage {stripAngle b u L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hLu : L ≤ u * Real.sin stripAngle)
    (hLbu : L ≤ (b - u) * Real.sin stripAngle) (q : flatShearedStrip (conePhase stripAngle) b)
    (hq : dist q.1 (flatShearedPoint (conePhase stripAngle) 0 u) ≤ L) :
    q ∈ range (translatedStripEdgeSource hs hLu hLbu) := by
  have hi : q.1 ∈ translatedStripCornerRigid stripAngle u '' flatLinkSectorDisk Real.pi L := by
    rw [translatedStripEdgeRigid_image hs hLu hLbu]
    exact ⟨q.2, hq⟩
  obtain ⟨w, hw, he⟩ := hi
  exact ⟨⟨w, hw⟩, Subtype.ext he⟩

def translatedStripBottomCornerSource {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b * Real.sin stripAngle) :
    flatLinkSectorDisk stripAngle L → flatShearedStrip (conePhase stripAngle) b := fun w ↦
  ⟨w.1, by
    have hw : w.1 ∈ flatShearedStrip (conePhase stripAngle) b ∩ closedBall (0 : ℂ) L := by
      rw [← translatedStripBottomCorner_image stripAngle_pos stripAngle_lt_pi hL]
      exact w.2
    exact hw.1⟩

theorem translatedStripBottomCornerSource_isometry {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b * Real.sin stripAngle) :
    Isometry (translatedStripBottomCornerSource stripAngle_pos stripAngle_lt_pi hL) := by
  apply Isometry.of_dist_eq
  intro w z
  rfl

theorem translatedStripBottomCornerSource_local_coverage {stripAngle b L : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hL : L ≤ b * Real.sin stripAngle)
    (q : flatShearedStrip (conePhase stripAngle) b) (hq : ‖q.1‖ ≤ L) :
    q ∈ range (translatedStripBottomCornerSource stripAngle_pos stripAngle_lt_pi hL) := by
  have hi : q.1 ∈ flatLinkSectorDisk stripAngle L := by
    rw [translatedStripBottomCorner_image stripAngle_pos stripAngle_lt_pi hL]
    exact ⟨q.2, by simpa only [mem_closedBall, dist_zero_right] using hq⟩
  exact ⟨⟨q.1, hi⟩, Subtype.ext rfl⟩

/-- The entire top ray is characterized by equality in the upper supporting
halfplane, using actual source membership to enforce nonnegative ray time. -/
theorem translatedStrip_mem_top_iff_im {stripAngle b : ℝ}
    (hs : 0 < Real.sin stripAngle) (hb : 0 ≤ b) (q : flatShearedStrip (conePhase stripAngle) b) :
    q ∈ range (translatedStripTop hb) ↔ q.1.im = b * Real.sin stripAngle := by
  constructor
  · rintro ⟨r, rfl⟩
    simp [translatedStripTop, flatShearedPoint, conePhase_im]
  · intro hq
    obtain ⟨r, hr, u, hu, hqu⟩ := q.2
    have hi : u * Real.sin stripAngle = b * Real.sin stripAngle := by
      simpa only [hqu, flatShearedPoint, Complex.add_im, Complex.mul_im,
        Complex.ofReal_im, Complex.ofReal_re, conePhase_im, zero_mul, zero_add, add_zero] using hq
    have hub : u = b := mul_right_cancel₀ hs.ne' hi
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    change flatShearedPoint (conePhase stripAngle) r b = q.1
    rw [hqu, hub]

/-- Exact top-ray preimage: it is the whole halfdisk diameter, including
both orientations and the center. No endpoint membership is postulated. -/
theorem translatedStripTopSource_mem_top_iff {stripAngle b t L : ℝ}
    (hs : 0 < Real.sin stripAngle) (hb : 0 ≤ b)
    (hLb : L ≤ b * Real.sin stripAngle) (hLt : L ≤ t * Real.sin stripAngle)
    (w : flatLinkSectorDisk Real.pi L) :
    translatedStripTopSource hs hLb hLt w ∈ range (translatedStripTop hb) ↔
      w.1.im = 0 := by
  rw [translatedStrip_mem_top_iff_im hs hb]
  change (flatShearedPoint (conePhase stripAngle) t b - w.1).im =
    b * Real.sin stripAngle ↔ w.1.im = 0
  simp only [Complex.sub_im, flatShearedPoint, Complex.add_im,
    Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    conePhase_im, zero_mul, zero_add]
  constructor <;> intro h <;> linarith

end RepulsiveCoulomb
