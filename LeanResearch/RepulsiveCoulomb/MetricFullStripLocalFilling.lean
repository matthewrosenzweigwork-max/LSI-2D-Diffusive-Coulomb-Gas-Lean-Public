import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskTwoAnchorUniqueness
import LeanResearch.RepulsiveCoulomb.MetricFlatDiskPatchExtension

/-! Source-only, uncompiled. Genuine whole-ball charts imply actual local
surjectivity of a strip image, including its bottom. This is derived by rigid
extension and two-anchor halfdisk uniqueness, not supplied as a contact field. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem metricFlatSubset_range_mem_nhds_of_interior
    {Y : Type*} [MetricSpace Y] {U : Set ℂ}
    (f : U → Y) (hf : Isometry f) (q : U) (hq : q.1 ∈ interior U)
    (C : MetricFlatDiskChart Y (f q)) : range f ∈ 𝓝 (f q) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  let ε := min r C.radius
  have hε : 0 < ε := lt_min hr C.radius_pos
  have hBU : ball q.1 ε ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hrU
  have hBR : ball q.1 ε ⊆ ball q.1 C.radius := ball_subset_ball (min_le_right _ _)
  have hoverlap : (interior (U ∩ ball q.1 C.radius)).Nonempty := by
    refine ⟨q.1, ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hε))
      (fun z hz ↦ ⟨hBU hz, hBR hz⟩)
  obtain ⟨g, hg, hagree, hrange⟩ := exists_flat_disk_patch_extension f hf q C hoverlap
  have hcenter := hagree q (mem_ball_self C.radius_pos)
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hyR : y ∈ ball (f q) C.radius := (ball_subset_ball (min_le_right _ _)) hy
  obtain ⟨z, hzy⟩ := hrange.symm ▸ hyR
  have hzε : z.1 ∈ ball q.1 ε := by
    have hdist : dist z (⟨q.1, mem_ball_self C.radius_pos⟩ : ball q.1 C.radius) =
        dist y (f q) := by
      calc
        _ = dist (g z) (g ⟨q.1, mem_ball_self C.radius_pos⟩) :=
          (hg.dist_eq _ _).symm
        _ = dist y (f q) := congrArg₂ dist hzy hcenter
    exact hdist.trans_lt hy
  exact ⟨⟨z.1, hBU hzε⟩, (hagree ⟨z.1, hBU hzε⟩ z.2).symm.trans hzy⟩

theorem fullNormalStrip_mem_interior {h : ℝ} {z : ℂ}
    (hz0 : 0 < z.im) (hzh : z.im < h) : z ∈ interior (flatFullNormalStrip h) := by
  have hopen : IsOpen {w : ℂ | 0 < w.im ∧ w.im < h} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hopen.mem_nhds ⟨hz0, hzh⟩) (fun w hw ↦ ⟨hw.1.le, hw.2.le⟩))

theorem metricFullStrip_range_mem_nhds_at_bottom
    {Y : Type*} [MetricSpace Y] (line : ℝ → Y) (hline : Isometry line)
    {h : ℝ} (hh : 0 < h) (f : flatFullNormalStrip h → Y) (hf : Isometry f)
    (hb : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip h,
      f ⟨(r : ℂ), hr⟩ = line r)
    (r : ℝ) (C : MetricFlatHalfDiskChart Y (line r)) : range f ∈ 𝓝 (line r) := by
  let L := C.radius / 2
  have hL : 0 < L := half_pos C.radius_pos
  have hLR : L < C.radius := half_lt_self C.radius_pos
  let rho : Icc (-L) L → Y := fun t ↦ line (r + t.1)
  have hrho : Isometry rho := by
    apply Isometry.of_dist_eq
    intro t u
    rw [hline.dist_eq]
    exact dist_add_left r t.1 u.1
  have hrho0 : rho (complexSymmetricIntervalZero hL) = line r := by
    simp [rho, complexSymmetricIntervalZero]
  obtain ⟨e, he0, heline⟩ := C.exists_aligned_to_short_interval hL hLR rho hrho hrho0
  let ε := min h C.radius / 2
  have hε : 0 < ε := half_pos (lt_min hh C.radius_pos)
  have hεh : ε < h := (half_lt_self (lt_min hh C.radius_pos)).trans_le (min_le_left _ _)
  have hεR : ε < C.radius :=
    (half_lt_self (lt_min hh C.radius_pos)).trans_le (min_le_right _ _)
  have hre (s : ℝ) : (s : ℂ) ∈ flatFullNormalStrip h := by
    simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hh.le
  have hzero : (0 : ℂ) ∈ flatUpperDisk C.radius := (flatUpperDiskZero C.radius_pos).2
  have hanchor : (L : ℂ) ∈ flatUpperDisk C.radius := by
    simp [flatUpperDisk, abs_of_pos hL, hLR]
  have heL : (e ⟨(L : ℂ), hanchor⟩).1 = line (r + L) := by
    simpa only [rho, halfDiskIntervalReal] using heline ⟨L, by constructor <;> linarith⟩
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hyR : y ∈ ball (line r) C.radius := hy.trans hεR
  let w : flatUpperDisk C.radius := e.symm ⟨y, hyR⟩
  have hew : (e w).1 = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hyR⟩)
  have hwnorm : ‖w.1‖ = dist y (line r) := by
    calc
      ‖w.1‖ = dist w (flatUpperDiskZero C.radius_pos) := by
        change ‖w.1‖ = dist w.1 0
        rw [dist_zero_right]
      _ = dist (e w) (e (flatUpperDiskZero C.radius_pos)) := (e.dist_eq _ _).symm
      _ = dist y (line r) := by change dist (e w).1 (e (flatUpperDiskZero C.radius_pos)).1 = _; rw [hew, he0]
  have hwε : ‖w.1‖ < ε := hwnorm.trans_lt hy
  have hwim : w.1.im ≤ ‖w.1‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
  let z : flatFullNormalStrip h := ⟨(r : ℂ) + w.1, by
    change 0 ≤ ((r : ℂ) + w.1).im ∧ ((r : ℂ) + w.1).im ≤ h
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using
      And.intro w.2.2 ((hwim.trans_lt hwε).le.trans hεh.le)⟩
  have hz0 : dist z.1 (r : ℂ) = ‖w.1‖ := by
    change dist ((r : ℂ) + w.1) (r : ℂ) = ‖w.1‖
    calc
      _ = dist w.1 0 := by simpa only [add_zero] using dist_add_left (r : ℂ) w.1 0
      _ = ‖w.1‖ := dist_zero_right _
  have hzL : dist z.1 ((r + L : ℝ) : ℂ) = dist w.1 (L : ℂ) := by
    change dist ((r : ℂ) + w.1) ((r + L : ℝ) : ℂ) = _
    rw [Complex.ofReal_add, dist_add_left]
  have hfx0 : dist (f z) (line r) = ‖w.1‖ := by
    calc
      _ = dist (f z) (f ⟨(r : ℂ), hre r⟩) :=
        congrArg (dist (f z)) (hb r (hre r)).symm
      _ = dist z.1 (r : ℂ) := hf.dist_eq z ⟨(r : ℂ), hre r⟩
      _ = ‖w.1‖ := hz0
  have hfzR : f z ∈ ball (line r) C.radius := hfx0.trans_lt (hwε.trans hεR)
  have hezero : (e ⟨0, hzero⟩).1 = line r := by
    simpa only [flatUpperDiskZero] using he0
  have heq : (⟨f z, hfzR⟩ : ball (line r) C.radius) = ⟨y, hyR⟩ := by
    apply metricHalfDisk_two_anchor_unique e (ne_of_lt hL) hzero hanchor
    · change dist (f z) (e ⟨0, hzero⟩).1 = dist y (e ⟨0, hzero⟩).1
      rw [hezero, hfx0, hwnorm]
    · have hfxL : dist (f z) (line (r + L)) = dist w.1 (L : ℂ) := by
        rw [← hb (r + L) (hre (r + L)), hf.dist_eq]
        exact hzL
      change dist (f z) (e ⟨(L : ℂ), hanchor⟩).1 = dist y (e ⟨(L : ℂ), hanchor⟩).1
      rw [heL, hfxL]
      calc
        dist w.1 (L : ℂ) = dist (e w) (e ⟨(L : ℂ), hanchor⟩) :=
          (e.dist_eq w ⟨(L : ℂ), hanchor⟩).symm
        _ = dist y (line (r + L)) := by
          change dist (e w).1 (e ⟨(L : ℂ), hanchor⟩).1 = _
          rw [hew, heL]
  exact ⟨z, congrArg Subtype.val heq⟩

/-- Translate an actual upper halfdisk into the strip; its source metric is
Euclidean, not the max metric on a real product. -/
def fullStripHalfDiskInclusion {h ε : ℝ} (hεh : ε ≤ h) (r : ℝ) :
    flatUpperDisk ε → flatFullNormalStrip h := fun z ↦
  ⟨(r : ℂ) + z.1, by
    change 0 ≤ ((r : ℂ) + z.1).im ∧ ((r : ℂ) + z.1).im ≤ h
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact ⟨z.2.2, ((le_abs_self z.1.im).trans (Complex.abs_im_le_norm z.1)).trans
      (z.2.1.le.trans hεh)⟩⟩

/-- The derived local filling constructs a WHOLE metric halfdisk whose
coordinates are the strip coordinates. Vertical strip segments consequently
have an actual inward normal germ in a genuine retained halfdisk chart. -/
theorem metricFullStrip_exists_coordinate_halfdisk
    {Y : Type*} [MetricSpace Y] (line : ℝ → Y) (hline : Isometry line)
    {h : ℝ} (hh : 0 < h) (f : flatFullNormalStrip h → Y) (hf : Isometry f)
    (hb : ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ flatFullNormalStrip h,
      f ⟨(q : ℂ), hq⟩ = line q)
    (r : ℝ) (C : MetricFlatHalfDiskChart Y (line r)) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ hεh : ε ≤ h,
      ∃ e : flatUpperDisk ε ≃ᵢ ball (line r) ε,
        (e (flatUpperDiskZero hε)).1 = line r ∧
        ∀ z, (e z).1 = f (fullStripHalfDiskInclusion hεh r z) := by
  obtain ⟨d, hd, hdF⟩ := Metric.mem_nhds_iff.mp
    (metricFullStrip_range_mem_nhds_at_bottom line hline hh f hf hb r C)
  let ε := min d h / 2
  have hε : 0 < ε := half_pos (lt_min hd hh)
  have hεd : ε ≤ d := (half_le_self (le_min hd.le hh.le)).trans (min_le_left _ _)
  have hεh : ε ≤ h := (half_le_self (le_min hd.le hh.le)).trans (min_le_right _ _)
  let inc := fullStripHalfDiskInclusion hεh r
  have hinc : Isometry inc := by
    apply Isometry.of_dist_eq
    intro z w
    change dist ((r : ℂ) + z.1) ((r : ℂ) + w.1) = dist z.1 w.1
    exact dist_add_left (r : ℂ) z.1 w.1
  have hr : (r : ℂ) ∈ flatFullNormalStrip h := by
    simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hh.le
  have hinc0 : inc (flatUpperDiskZero hε) = ⟨(r : ℂ), hr⟩ := by
    apply Subtype.ext
    simp [inc, fullStripHalfDiskInclusion, flatUpperDiskZero]
  have hball (z : flatUpperDisk ε) : f (inc z) ∈ ball (line r) ε := by
    rw [mem_ball, ← hb r hr, ← hinc0, hf.dist_eq, hinc.dist_eq]
    change dist z.1 0 < ε
    rw [dist_zero_right]
    exact z.2.1
  let g : flatUpperDisk ε → ball (line r) ε := fun z ↦ ⟨f (inc z), hball z⟩
  have hg : Isometry g := by
    apply Isometry.of_dist_eq
    intro z w
    exact (hf.comp hinc).dist_eq z w
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, hz⟩ := hdF ((ball_subset_ball hεd) y.2)
    have hnorm : ‖z.1 - (r : ℂ)‖ < ε := by
      rw [← dist_eq_norm]
      change dist z (⟨(r : ℂ), hr⟩ : flatFullNormalStrip h) < ε
      rw [← hf.dist_eq, hb r hr, hz]
      exact y.2
    let w : flatUpperDisk ε := ⟨z.1 - (r : ℂ), hnorm, by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using z.2.1⟩
    have hw : inc w = z := by
      apply Subtype.ext
      change (r : ℂ) + (z.1 - (r : ℂ)) = z.1
      ring
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change f (inc w) = y.1
    rw [hw, hz]
  let e : flatUpperDisk ε ≃ᵢ ball (line r) ε :=
    { Equiv.ofBijective g ⟨hg.injective, hsurj⟩ with isometry_toFun := hg }
  refine ⟨ε, hε, hεh, e, ?_, fun _ ↦ rfl⟩
  change f (inc (flatUpperDiskZero hε)) = line r
  rw [hinc0, hb r hr]

end RepulsiveCoulomb
