module

public import LeanResearch.RepulsiveCoulomb.FullStripResidualSource
public import LeanResearch.RepulsiveCoulomb.MetricFlatDiskPatchExtension
public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment
public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskTwoAnchorUniqueness

@[expose] public section

/-! Isometries are NOT asserted open in an arbitrary metric plane. Interior
fullness is proved by actual Euclidean rigidity in a whole disk chart. Bottom
fullness is proved by a whole retained halfdisk and two real anchor distances. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem metricFlatDisk_isometry_locally_full {Y : Type*} [MetricSpace Y]
    {U : Set ℂ} (F : U → Y) (hF : Isometry F) (q : U)
    (C : MetricFlatDiskChart Y (F q)) {ε : ℝ} (hε : 0 < ε)
    (hεC : ε ≤ C.radius) (hball : ball q.1 ε ⊆ U) :
    ball (F q) ε ⊆ range F := by
  let i : ball q.1 ε → U := fun z ↦ ⟨z.1, hball z.2⟩
  have htarget (z : ball q.1 ε) : F (i z) ∈ ball (F q) C.radius := by
    rw [mem_ball, hF.dist_eq]
    exact z.2.trans_le hεC
  let τ : ball q.1 ε → ℂ := fun z ↦ (C.toEuclidean ⟨F (i z), htarget z⟩).1
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (C.toEuclidean ⟨F (i z), htarget z⟩)
      (C.toEuclidean ⟨F (i w), htarget w⟩) = dist z w
    rw [C.toEuclidean.dist_eq]
    exact hF.dist_eq (i z) (i w)
  obtain ⟨e, he⟩ := exists_complex_isometry_extension_of_open_overlap τ hτ
    (by rw [isOpen_ball.interior_eq]; exact ⟨q.1, mem_ball_self hε⟩)
  have heq : e q.1 = 0 := (he ⟨q.1, mem_ball_self hε⟩).trans C.center
  intro z hz
  let w : ball (0 : ℂ) C.radius := C.toEuclidean ⟨z, hz.trans_le hεC⟩
  have hwn : dist w.1 0 = dist z (F q) := by
    calc
      dist w.1 0 =
          dist w.1 (C.toEuclidean ⟨F q, mem_ball_self C.radius_pos⟩).1 :=
        congrArg (dist w.1) C.center.symm
      _ = dist z (F q) :=
        C.toEuclidean.dist_eq ⟨z, hz.trans_le hεC⟩
          ⟨F q, mem_ball_self C.radius_pos⟩
  have hx : e.symm w.1 ∈ ball q.1 ε := by
    rw [mem_ball, ← e.dist_eq, e.apply_symm_apply, heq, hwn]
    exact hz
  refine ⟨i ⟨e.symm w.1, hx⟩, ?_⟩
  have ht := he ⟨e.symm w.1, hx⟩
  rw [e.apply_symm_apply] at ht
  have hc : C.toEuclidean ⟨F (i ⟨e.symm w.1, hx⟩), htarget _⟩ =
      C.toEuclidean ⟨z, hz.trans_le hεC⟩ := Subtype.ext ht.symm
  exact congrArg Subtype.val (C.toEuclidean.injective hc)

/-- At the old edge, the aligned halfdisk covers a positive relative target
ball. Its proof uses the ACTUAL entire target halfdisk; a source-only halfdisk
or an angle number without local onto coverage would be insufficient. -/
theorem metricFullStrip_bottom_locally_full {Y : Type*} [MetricSpace Y]
    {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → Y) (hF : Isometry F)
    (r : ℝ) (C : MetricFlatHalfDiskChart Y (F (fullStripBottom hh.le r))) :
    ∃ ε : ℝ, 0 < ε ∧ ball (F (fullStripBottom hh.le r)) ε ⊆ range F := by
  let b := min h C.radius / 4
  have hb : 0 < b := div_pos (lt_min hh C.radius_pos) (by norm_num)
  have hbh : b < h := by dsimp [b]; linarith [min_le_left h C.radius, lt_min hh C.radius_pos]
  have hbC : b < C.radius := by dsimp [b]; linarith [min_le_right h C.radius, lt_min hh C.radius_pos]
  let line : Icc (-b) b → Y := fun t ↦ F (fullStripBottom hh.le (r + t.1))
  have hline : Isometry line := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hF.dist_eq, (fullStripBottom_isometry hh.le).dist_eq]
    simp only [Real.dist_eq, add_sub_add_left_eq_sub]
    rfl
  have hzero : line (complexSymmetricIntervalZero hb) = F (fullStripBottom hh.le r) := by
    simp [line, complexSymmetricIntervalZero]
  obtain ⟨e, he0, hel⟩ := C.exists_aligned_to_short_interval hb hbC line hline hzero
  have h0 : (0 : ℂ) ∈ flatUpperDisk C.radius := by simp [flatUpperDisk, C.radius_pos]
  have hbreal : (b : ℂ) ∈ flatUpperDisk C.radius := by simp [flatUpperDisk, abs_of_pos hb, hbC]
  have heA : (e ⟨(0 : ℂ), h0⟩).1 = F (fullStripBottom hh.le r) := he0
  have heB : (e ⟨(b : ℂ), hbreal⟩).1 = F (fullStripBottom hh.le (r + b)) :=
    hel ⟨b, by linarith, le_rfl⟩
  refine ⟨b, hb, ?_⟩
  intro z hz
  let zB : ball (F (fullStripBottom hh.le r)) C.radius := ⟨z, hz.trans hbC⟩
  let w : flatUpperDisk C.radius := e.symm zB
  have hw : ‖w.1‖ < b := by
    have heq : dist w (⟨(0 : ℂ), h0⟩ : flatUpperDisk C.radius) =
        dist z (F (fullStripBottom hh.le r)) := by
      rw [← e.dist_eq, e.apply_symm_apply]
      exact congrArg (dist z) heA
    simpa only [Subtype.dist_eq, dist_zero_right] using heq.trans_lt hz
  have hsource : w.1 + (r : ℂ) ∈ flatFullNormalStrip h := by
    refine ⟨by simpa using w.2.2, ?_⟩
    have him := (le_abs_self w.1.im).trans (Complex.abs_im_le_norm w.1)
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using him.trans (hw.le.trans hbh.le)
  let x : flatFullNormalStrip h := ⟨w.1 + (r : ℂ), hsource⟩
  have hxball : F x ∈ ball (F (fullStripBottom hh.le r)) C.radius := by
    rw [mem_ball, hF.dist_eq]
    change dist (w.1 + (r : ℂ)) (r : ℂ) < C.radius
    simpa only [dist_eq_norm, add_sub_cancel_right] using hw.trans hbC
  let xB : ball (F (fullStripBottom hh.le r)) C.radius := ⟨F x, hxball⟩
  have hdist (t : ℝ) (ht : (t : ℂ) ∈ flatUpperDisk C.radius)
      (het : (e ⟨(t : ℂ), ht⟩).1 = F (fullStripBottom hh.le (r + t))) :
      dist xB (e ⟨(t : ℂ), ht⟩) = dist zB (e ⟨(t : ℂ), ht⟩) := by
    have hleft : dist xB (e ⟨(t : ℂ), ht⟩) = dist w.1 (t : ℂ) := by
      change dist (F x) (e ⟨(t : ℂ), ht⟩).1 = _
      rw [het, hF.dist_eq]
      change dist (w.1 + (r : ℂ)) ((r + t : ℝ) : ℂ) = _
      rw [Complex.ofReal_add, add_comm (r : ℂ) (t : ℂ), dist_add_right]
    rw [hleft, ← e.symm.dist_eq, e.symm_apply_apply]
    rfl
  have hxz : xB = zB := metricHalfDisk_two_anchor_unique e (by exact ne_of_lt hb)
    h0 hbreal (hdist 0 h0 (by simpa using heA)) (hdist b hbreal heB)
  exact ⟨x, congrArg Subtype.val hxz⟩

/-- The open strip below the completed top is relatively open in its target.
Every local surjectivity statement is derived in the preceding two lemmas. -/
theorem metricFullStrip_without_top_open {Y : Type*} [MetricSpace Y]
    {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → Y) (hF : Isometry F)
    (hbottom : ∀ r, Nonempty (MetricFlatHalfDiskChart Y (F (fullStripBottom hh.le r))))
    (hinterior : ∀ z, 0 < z.1.im → z.1.im < h → Nonempty (MetricFlatDiskChart Y (F z))) :
    IsOpen (range F \ range (F ∘ fullStripTop hh.le)) := by
  have htopclosed : IsClosed (range (F ∘ fullStripTop hh.le)) :=
    (hF.comp (fullStripTop_isometry hh.le)).isClosedEmbedding.isClosed_range
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨⟨z, rfl⟩, hz⟩
  have hzt : z.1.im < h := lt_of_le_of_ne z.2.2
    (fun he ↦ hz ((fullStrip_image_mem_top_iff hh.le hF.injective z).mpr he))
  have hfill : ∃ ε : ℝ, 0 < ε ∧ ball (F z) ε ⊆ range F := by
    by_cases hz0 : z.1.im = 0
    · have he : fullStripBottom hh.le z.1.re = z := Subtype.ext (Complex.ext rfl hz0.symm)
      obtain ⟨C⟩ := hbottom z.1.re
      simpa only [he] using metricFullStrip_bottom_locally_full hh F hF z.1.re C
    · have hzpos : 0 < z.1.im := lt_of_le_of_ne z.2.1 (Ne.symm hz0)
      obtain ⟨C⟩ := hinterior z hzpos hzt
      let ε := min C.radius (min z.1.im (h - z.1.im)) / 2
      have hε : 0 < ε := half_pos (lt_min C.radius_pos (lt_min hzpos (sub_pos.mpr hzt)))
      have hεmin : ε ≤ min C.radius (min z.1.im (h - z.1.im)) :=
        half_le_self (le_of_lt (lt_min C.radius_pos (lt_min hzpos (sub_pos.mpr hzt))))
      have hεC : ε ≤ C.radius := hεmin.trans (min_le_left _ _)
      have hεlo : ε ≤ z.1.im :=
        hεmin.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hεhi : ε ≤ h - z.1.im :=
        hεmin.trans ((min_le_right _ _).trans (min_le_right _ _))
      refine ⟨ε, hε, metricFlatDisk_isometry_locally_full F hF z C hε hεC ?_⟩
      intro w hw
      have him : |w.im - z.1.im| ≤ ‖w - z.1‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z.1)
      have hwn : ‖w - z.1‖ < ε := by
        simpa only [mem_ball, dist_eq_norm] using hw
      have hi : |w.im - z.1.im| < ε := him.trans_lt hwn
      have hai := abs_lt.mp hi
      exact ⟨by linarith, by linarith⟩
  obtain ⟨ε, hε, hfill⟩ := hfill
  exact Filter.mem_of_superset
    (Filter.inter_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) (htopclosed.isOpen_compl.mem_nhds hz))
    (fun _ hw ↦ ⟨hfill hw.1, hw.2⟩)

end RepulsiveCoulomb
