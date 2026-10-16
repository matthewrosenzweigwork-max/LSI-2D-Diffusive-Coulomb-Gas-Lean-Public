module

public import LeanResearch.RepulsiveCoulomb.PointFullLineUniformNormalStrip
public import LeanResearch.RepulsiveCoulomb.FullNormalStripWidthClosure

@[expose] public section

/-! Source-only, uncompiled. Every subcritical width is instantiated from the
selected full-line rectangle continuation. Cross-width compatibility is proved
from the actual halfdisk and zero-exponent charts, then completeness constructs
width h. No strip family, normality, compatibility or attainment is an input. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem pointFullNormalStrip_positive_height_interior
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ}
    (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    (hboundary : frontier P = range line)
    {s : ℝ} (hs : 0 ≤ s) (F : flatFullNormalStrip s → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hb : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip s,
      (F ⟨(r : ℂ), hr⟩).1 = line r) :
    ∀ z, 0 < z.1.im → (F z).1 ∈ interior P := by
  intro z hz
  have hr (r : ℝ) : (r : ℂ) ∈ flatFullNormalStrip s := by
    simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hs
  have hnoreturn := pointFlatStage_no_full_line_return line hline F hF
    (by norm_num : (0 : ℝ) ≠ 1) (hr 0) (hr 1) (hb 0 (hr 0)) (hb 1 (hr 1)) z hz
  by_contra hn
  exact hnoreturn (hboundary ▸ (show (F z).1 ∈ frontier P from
    ⟨subset_closure (F z).2, hn⟩))

theorem pointFullNormalStrip_avoids_marks_below_height
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P S : Set ℂ}
    (line : ℝ → ℂ) {h s : ℝ} (hs : 0 ≤ s)
    (hbound : ∀ p ∈ S, ∀ r : ℝ, h ≤ (pointSmoothConformalEDist a y p (line r)).toReal)
    (F : flatFullNormalStrip s → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hb : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip s,
      (F ⟨(r : ℂ), hr⟩).1 = line r) :
    ∀ z, z.1.im < h → (F z).1 ∉ S := by
  intro z hz hp
  have hr : (z.1.re : ℂ) ∈ flatFullNormalStrip s := by
    simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hs
  have hd := hF z ⟨(z.1.re : ℂ), hr⟩
  rw [hb z.1.re hr] at hd
  have hsource : dist z (⟨(z.1.re : ℂ), hr⟩ : flatFullNormalStrip s) = z.1.im := by
    change dist z.1 (z.1.re : ℂ) = z.1.im
    have he : z.1 = flatShearedPoint Complex.I z.1.re z.1.im := by
      apply Complex.ext <;> simp [flatShearedPoint]
    calc
      dist z.1 (z.1.re : ℂ) =
          dist (flatShearedPoint Complex.I z.1.re z.1.im) (z.1.re : ℂ) :=
        congrArg (fun v : ℂ => dist v (z.1.re : ℂ)) he
      _ = z.1.im := by
        simpa only [flatShearedPoint_zero] using
          (flatShearedPoint_dist_bottom (v := Complex.I) (by simp) z.1.re z.2.1)
  rw [hsource] at hd
  have hle := hbound (F z).1 hp z.1.re
  rw [hd] at hle
  exact hz.not_ge hle

theorem point_exists_fullNormalStrip_at_marked_distance
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    (hboundary : frontier P = range line)
    (nu : ℂ → ℝ)
    (hnu : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      nu p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo))
    {S : Set ℂ}
    (hmarkedInterior : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ S)
    (hmarkedBoundary : ∀ p ∈ frontier P, nu p ≠ 0 → p ∈ S)
    (hclean : Disjoint S (range line))
    {h : ℝ} (hh : 0 < h)
    (hbound : ∀ p ∈ S, ∀ r : ℝ, h ≤ (pointSmoothConformalEDist a y p (line r)).toReal) :
    ∃ F : flatFullNormalStrip h → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip h,
        (F ⟨(r : ℂ), hr⟩).1 = line r) ∧
      (∀ z, 0 < z.1.im → (F z).1 ∈ interior P) ∧
      (∀ z, z.1.im < h → (F z).1 ∉ S) ∧
      IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) := by
  have hfront (r : ℝ) : line r ∈ frontier P := by rw [hboundary]; exact mem_range_self r
  have hmem (r : ℝ) : line r ∈ P := hP.frontier_subset (hfront r)
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : CompleteSpace P := pointRegionMetricSpace_complete ha y hP
  let Line : ℝ → P := fun r ↦ ⟨line r, hmem r⟩
  have hLine : Isometry Line := Isometry.of_dist_eq hline
  have hH (r : ℝ) : Nonempty (MetricFlatHalfDiskChart P (Line r)) := by
    obtain ⟨C, hC⟩ := hnu (line r) (hfront r)
    have hn : nu (line r) = 0 := by
      by_contra hn
      exact disjoint_left.mp hclean (hmarkedBoundary _ (hfront r) hn) (mem_range_self r)
    have hw : C.flatPhysicalWidth = Real.pi := by
      rw [hn] at hC
      unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      nlinarith
    exact ⟨C.flatHalfDiskChart ha y (hmem r) hw⟩
  let H := fun r ↦ Classical.choice (hH r)
  have hex (s : Ioo (0 : ℝ) h) : ∃ f : flatFullNormalStrip s.1 → P,
      Isometry f ∧ ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip s.1,
        f ⟨(r : ℂ), hr⟩ = Line r := by
    obtain ⟨f, hf, hb⟩ := point_exists_fullLine_uniform_normal_strip_of_clearance
      ha y hP Line hLine hboundary H hmarkedInterior s.2.1
      (fun p hp r ↦ s.2.2.trans_le (hbound p hp r))
    exact ⟨f, Isometry.of_dist_eq hf, hb⟩
  choose f hf hb using hex
  have hreg (s : Ioo (0 : ℝ) h) (z : flatFullNormalStrip s.1) (hz : 0 < z.1.im) :
      Nonempty (MetricFlatDiskChart P (f s z)) := by
    have hi := pointFullNormalStrip_positive_height_interior line hline hboundary s.2.1.le
      (f s) (fun x z ↦ (hf s).dist_eq x z) (fun r hr ↦ congrArg Subtype.val (hb s r hr)) z hz
    have hn := pointFullNormalStrip_avoids_marks_below_height line s.2.1.le hbound
      (f s) (fun x z ↦ (hf s).dist_eq x z) (fun r hr ↦ congrArg Subtype.val (hb s r hr))
      z (z.2.2.trans_lt s.2.2)
    have he : coalescedPointExponent a y (f s z).1 = 0 := by
      by_contra he
      exact hn (hmarkedInterior _ hi he)
    exact exists_pointInterior_zeroExponent_flatDiskChart ha y hi he
  have hagree (s t : Ioo (0 : ℝ) h) (hst : s.1 ≤ t.1) (z : flatFullNormalStrip s.1) :
      f s z = f t ⟨z.1, flatFullNormalStrip_mono hst z.2⟩ := by
    let R := |z.1.re| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    let K := flatNormalRectangle (-R) R s.1
    have hzK : z.1 ∈ K := ⟨⟨by dsimp [R]; linarith [neg_abs_le z.1.re],
      by dsimp [R]; linarith [le_abs_self z.1.re]⟩, z.2⟩
    let fs : K → P := fun w ↦ f s ⟨w.1, w.2.2⟩
    have hfs : Isometry fs := (hf s).comp (show Isometry (fun w : K ↦
      (⟨w.1, w.2.2⟩ : flatFullNormalStrip s.1)) from fun _ _ ↦ rfl)
    have hKt : K ⊆ flatFullNormalStrip t.1 := fun _ hw ↦ flatFullNormalStrip_mono hst hw.2
    have hwindow : ∀ r ∈ Icc (0 - R / 2) (0 + R / 2), (r : ℂ) ∈ K := by
      intro r hr
      change r ∈ Icc (-R) R ∧ (0 : ℝ) ∈ Icc 0 s.1
      exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, le_rfl, s.2.1.le⟩
    exact metricFullLine_stages_agree Line hLine 0 0
      (by simpa only [zero_add] using H 0)
      (flatNormalRectangle_convex _ _ _) (flatNormalRectangle_compact _ _ _).isClosed
      (flatNormalRectangle_interior_nonempty (by linarith) s.2.1) hKt (half_pos hR) hwindow
      fs (f t) hfs (hf t)
      (fun r hr ↦ by simpa only [zero_add] using hb s r hr.2)
      (fun r hr ↦ by simpa only [zero_add] using hb t r hr)
      (fun w hw ↦ hreg s ⟨w.1, w.2.2⟩ (flatNormalRectangle_interior_im_pos hw)) ⟨z.1, hzK⟩
  have hcompat : ∀ s t : Ioo (0 : ℝ) h, ∀ z (hs : z ∈ flatFullNormalStrip s.1)
      (ht : z ∈ flatFullNormalStrip t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩ := by
    intro s t z hs ht
    rcases le_total s.1 t.1 with hst | hts
    · exact hagree s t hst ⟨z, hs⟩
    · exact (hagree t s hts ⟨z, ht⟩).symm
  obtain ⟨F, hF, hFold⟩ := exists_fullNormalStrip_width_limit hh f hf hcompat
  let s0 : Ioo (0 : ℝ) h := ⟨h / 2, half_pos hh, half_lt_self hh⟩
  have hFb : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip h,
      (F ⟨(r : ℂ), hr⟩).1 = line r := by
    intro r hr
    have hr0 : (r : ℂ) ∈ flatFullNormalStrip s0.1 := by
      simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) s0.2.1.le
    exact congrArg Subtype.val ((hFold s0 ⟨(r : ℂ), hr0⟩).trans (hb s0 r hr0))
  have hd : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z :=
    fun x z ↦ hF.dist_eq x z
  have hFi : @Isometry (flatFullNormalStrip h) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace (fun z ↦ (F z).1) :=
    @Isometry.of_dist_eq _ ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace _ hd
  have hc := @flatFullNormalStrip_isometry_closed_proper ℂ (pointSmoothConformalMetricSpace ha y)
    h (fun z ↦ (F z).1) hFi
  rw [pointSmoothConformalMetricSpace_topology ha y] at hc
  exact ⟨F, hd, hFb,
    pointFullNormalStrip_positive_height_interior line hline hboundary hh.le F hd hFb,
    pointFullNormalStrip_avoids_marks_below_height line hh.le hbound F hd hFb, hc.1, hc.2⟩

end RepulsiveCoulomb
