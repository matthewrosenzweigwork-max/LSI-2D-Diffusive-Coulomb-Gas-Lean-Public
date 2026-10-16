import LeanResearch.RepulsiveCoulomb.MetricCleanRayHalfDiskPatches
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskTwoAnchorUniqueness

/-! Successor source-only draft. Actual overlap geometry for bottom halfdisks.
Projection to the common real bottom gives real anchor points and quantitative
containment in a larger original chart. These are geometric facts, not assumed
transition compatibility. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Orthogonal projection to the real axis decreases distance to every real
bottom point, and its transverse displacement has the same bound. -/
theorem complex_real_projection_dist_bounds (z : ℂ) (r : ℝ) :
    dist (z.re : ℂ) (r : ℂ) ≤ dist z (r : ℂ) ∧
      dist z (z.re : ℂ) ≤ dist z (r : ℂ) := by
  constructor
  · simpa only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (z - (r : ℂ))
  · rw [Complex.dist_of_re_eq (by simp), Real.dist_eq, Complex.ofReal_im, sub_zero,
      Complex.dist_eq]
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (z - (r : ℂ))

/-- Any nonempty pair of upper halfdisk overlaps contains two distinct actual
nonnegative real bottom parameters. The witnesses are constructed by a small
positive displacement of the orthogonal projection. -/
theorem flatRayHalfDisk_overlap_real_anchors {ri rj : ℝ} {εi εj : ℝ}
    (hεi : εi < ri) {z : ℂ}
    (hi : z ∈ flatRayHalfDisk ri εi) (hj : z ∈ flatRayHalfDisk rj εj) :
    ∃ s t : NNReal, s ≠ t ∧
      (s : ℂ) ∈ flatRayHalfDisk ri εi ∧ (s : ℂ) ∈ flatRayHalfDisk rj εj ∧
      (t : ℂ) ∈ flatRayHalfDisk ri εi ∧ (t : ℂ) ∈ flatRayHalfDisk rj εj := by
  let a := z.re
  have hai : dist (a : ℂ) (ri : ℂ) < εi :=
    (complex_real_projection_dist_bounds z ri).1.trans_lt hi.1
  have haj : dist (a : ℂ) (rj : ℂ) < εj :=
    (complex_real_projection_dist_bounds z rj).1.trans_lt hj.1
  have ha0 : 0 ≤ a := by
    have h := hai
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_lt.mp h).1]
  let η := min (εi - dist (a : ℂ) (ri : ℂ)) (εj - dist (a : ℂ) (rj : ℂ)) / 2
  have hη : 0 < η := half_pos (lt_min (sub_pos.mpr hai) (sub_pos.mpr haj))
  have hηi : η < εi - dist (a : ℂ) (ri : ℂ) :=
    (half_lt_self (lt_min (sub_pos.mpr hai) (sub_pos.mpr haj))).trans_le (min_le_left _ _)
  have hηj : η < εj - dist (a : ℂ) (rj : ℂ) :=
    (half_lt_self (lt_min (sub_pos.mpr hai) (sub_pos.mpr haj))).trans_le (min_le_right _ _)
  let s : NNReal := ⟨a, ha0⟩
  let t : NNReal := ⟨a + η, add_nonneg ha0 hη.le⟩
  have hst : s ≠ t := by
    intro he
    have he' : a = a + η := congrArg (fun q : NNReal ↦ (q : ℝ)) he
    linarith
  have hstep : dist ((a + η : ℝ) : ℂ) (a : ℂ) = η := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      add_sub_cancel_left, abs_of_pos hη]
  have hti : dist ((a + η : ℝ) : ℂ) (ri : ℂ) < εi := by
    have h := dist_triangle ((a + η : ℝ) : ℂ) (a : ℂ) (ri : ℂ)
    rw [hstep] at h
    linarith
  have htj : dist ((a + η : ℝ) : ℂ) (rj : ℂ) < εj := by
    have h := dist_triangle ((a + η : ℝ) : ℂ) (a : ℂ) (rj : ℂ)
    rw [hstep] at h
    linarith
  exact ⟨s, t, hst, ⟨hai, by simp⟩, ⟨haj, by simp⟩,
    ⟨hti, by simp⟩, ⟨htj, by simp⟩⟩

/-- An overlapping patch's point remains in the first patch's larger original
metric chart. The estimate is <2 epsilon_i and holds globally on the overlap. -/
theorem metricRay_halfDisk_overlap_image_mem_ball {Y : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ) (ri rj : NNReal) {εi εj R : ℝ}
    (hεi : εi < (ri : ℝ)) (hR : 2 * εi ≤ R)
    (F : flatRayHalfDisk rj εj → Y) (hF : Isometry F)
    (hbottom : ∀ t : NNReal, ∀ ht : (t : ℂ) ∈ flatRayHalfDisk rj εj,
      F ⟨(t : ℂ), ht⟩ = ρ t)
    {z : ℂ} (hi : z ∈ flatRayHalfDisk ri εi) (hj : z ∈ flatRayHalfDisk rj εj) :
    F ⟨z, hj⟩ ∈ ball (ρ ri) R := by
  have hai : dist (z.re : ℂ) (ri : ℂ) < εi :=
    (complex_real_projection_dist_bounds z ri).1.trans_lt hi.1
  have haj : dist (z.re : ℂ) (rj : ℂ) < εj :=
    (complex_real_projection_dist_bounds z rj).1.trans_lt hj.1
  have ha0 : 0 ≤ z.re := by
    have h := hai
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_lt.mp h).1]
  let t : NNReal := ⟨z.re, ha0⟩
  have htj : (t : ℂ) ∈ flatRayHalfDisk rj εj := ⟨haj, by simp⟩
  have hfirst : dist (F ⟨z, hj⟩) (ρ t) < εi := by
    rw [← hbottom t htj, hF.dist_eq]
    exact (complex_real_projection_dist_bounds z ri).2.trans_lt hi.1
  have hsecond : dist (ρ t) (ρ ri) < εi := by
    rw [hρ.dist_eq]
    change dist (z.re : ℝ) (ri : ℝ) < εi
    simpa only [Real.dist_eq, Complex.dist_eq, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hai
  have htri := dist_triangle (F ⟨z, hj⟩) (ρ t) (ρ ri)
  change dist (F ⟨z, hj⟩) (ρ ri) < R
  linarith

end RepulsiveCoulomb
