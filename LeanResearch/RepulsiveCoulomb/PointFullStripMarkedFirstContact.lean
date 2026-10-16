import LeanResearch.RepulsiveCoulomb.FiniteMarkedLineDistanceAttained
import LeanResearch.RepulsiveCoulomb.PointFullNormalStripAtMarkedDistance
import LeanResearch.RepulsiveCoulomb.MetricFullStripFirstContact
import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity
import LeanResearch.RepulsiveCoulomb.PointActualGeodesicUniqueness

/-! Source-only, uncompiled. First contact is constructed from actual retained
geometry, finite marks and the selected all-width strip predecessor. Contained
minimizers are derived from the genuine full/admissible retained cone charts.
Neither normality nor a top-contact/residual certificate is an input. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem point_exists_marked_first_contact_full_strip
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    (hboundary : frontier P = range line)
    (nu : ℂ → ℝ)
    (hnu : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      nu p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo))
    {S : Set ℂ} (hS : S.Finite) (hSne : S.Nonempty) (hSP : S ⊆ P)
    (hmarkedInterior : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ S)
    (hmarkedBoundary : ∀ p ∈ frontier P, nu p ≠ 0 → p ∈ S)
    (hclean : Disjoint S (range line)) :
    ∃ h : ℝ, ∃ hh : 0 < h, ∃ x ∈ S, ∃ r : ℝ,
      (pointSmoothConformalEDist a y x (line r)).toReal = h ∧
      (∀ p ∈ S, ∀ q : ℝ, h ≤ (pointSmoothConformalEDist a y p (line q)).toReal) ∧
      ∃ F : flatFullNormalStrip h → P,
        (∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w) ∧
        (∀ q : ℝ, ∀ hq : (q : ℂ) ∈ flatFullNormalStrip h,
          (F ⟨(q : ℂ), hq⟩).1 = line q) ∧
        (∀ z, 0 < z.1.im → (F z).1 ∈ interior P) ∧
        (∀ z, z.1.im < h → (F z).1 ∉ S) ∧
        (F (fullStripPoint r ⟨h, hh.le, le_rfl⟩)).1 = x ∧
        IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) := by
  obtain ⟨h, hh, x, hx, r, hdist, hbound⟩ := pointMarkedLine_distance_attained ha y line hline hS hSne hclean
  obtain ⟨F, hF, hFb, hFi, hFavoid, hFclosed, hFproper⟩ :=
    point_exists_fullNormalStrip_at_marked_distance ha y hP line hline hboundary nu hnu
      hmarkedInterior hmarkedBoundary hclean hh hbound
  have hfront (q : ℝ) : line q ∈ frontier P := by rw [hboundary]; exact mem_range_self q
  have hmem (q : ℝ) : line q ∈ P := hP.frontier_subset (hfront q)
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : TopologicalSpace P := M.toUniformSpace.toTopologicalSpace
  let Line : ℝ → P := fun q ↦ ⟨line q, hmem q⟩
  have hLine : Isometry Line := Isometry.of_dist_eq hline
  have hFiso : Isometry F := Isometry.of_dist_eq hF
  have hbottom : ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ flatFullNormalStrip h,
      F ⟨(q : ℂ), hq⟩ = Line q := fun q hq ↦ Subtype.ext (hFb q hq)
  have hH (q : ℝ) : Nonempty (MetricFlatHalfDiskChart P (Line q)) := by
    obtain ⟨C, hC⟩ := hnu (line q) (hfront q)
    have hn : nu (line q) = 0 := by
      by_contra hn
      exact disjoint_left.mp hclean (hmarkedBoundary _ (hfront q) hn) (mem_range_self q)
    have hw : C.flatPhysicalWidth = Real.pi := by
      rw [hn] at hC
      unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      nlinarith
    exact ⟨C.flatHalfDiskChart ha y (hmem q) hw⟩
  have hfill (z : flatFullNormalStrip h) (hz : z.1.im < h) : range F ∈ 𝓝 (F z) := by
    by_cases hz0 : 0 < z.1.im
    · have hzero : coalescedPointExponent a y (F z).1 = 0 := by
        by_contra hn
        exact hFavoid z hz (hmarkedInterior _ (hFi z hz0) hn)
      obtain ⟨C⟩ := exists_pointInterior_zeroExponent_flatDiskChart ha y (hFi z hz0) hzero
      exact metricFlatSubset_range_mem_nhds_of_interior F hFiso z (fullNormalStrip_mem_interior hz0 hz) C
    · have hzim : z.1.im = 0 := le_antisymm (le_of_not_gt hz0) z.2.1
      have hreal : z.1 = (z.1.re : ℂ) := by apply Complex.ext <;> simp [hzim]
      have hzreal : F z = Line z.1.re := by
        have hr : (z.1.re : ℂ) ∈ flatFullNormalStrip h := hreal ▸ z.2
        exact congrArg F (Subtype.ext hreal) |>.trans (hbottom z.1.re hr)
      rw [hzreal]
      exact metricFullStrip_range_mem_nhds_at_bottom Line hLine hh F hFiso hbottom z.1.re
        (Classical.choice (hH z.1.re))
  have hconv := (pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex ha y hP hconn hcharts).1
  obtain ⟨gamma, hg0, hg1, _, hgP, hgd⟩ := hconv (line r) (hmem r) x (hSP hx)
  have hL : (pointSmoothConformalEDist a y (line r) x).toReal = h := by
    rw [pointSmoothConformalEDist_comm]
    exact hdist
  let Gamma : unitInterval → P := fun t ↦ ⟨gamma t, hgP t⟩
  have hGamma : ∀ s t, dist (Gamma s) (Gamma t) = |t.1 - s.1| * h := by
    intro s t
    change (pointSmoothConformalEDist a y (gamma s) (gamma t)).toReal = _
    rw [hgd, hL]
  have hGammaLip : LipschitzWith ⟨h, hh.le⟩ Gamma := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hGamma]
    change |t.1 - s.1| * h ≤ h * |s.1 - t.1|
    rw [abs_sub_comm, mul_comm]
  have htop := metricFullStrip_nearest_endpoint_on_top Line hh F hFiso hbottom hfill r
    Gamma hGammaLip.continuous (Subtype.ext hg0) hGamma (by
      intro q
      change h ≤ (pointSmoothConformalEDist a y (gamma 1) (line q)).toReal
      rw [hg1]
      exact hbound x hx q)
  exact ⟨h, hh, x, hx, r, hdist, hbound, F, hF, hFb, hFi, hFavoid,
    (congrArg Subtype.val htop).trans hg1, hFclosed, hFproper⟩

/-- Once top contact is constructed, every minimizing segment from its nearest
bottom point is the literal vertical segment. This DERIVES the inward normal
germ. The local-filling theorem above makes the strip's small halfdisk a whole
relative metric chart, so this is geometric normality rather than a label. -/
theorem pointFullStrip_minimizer_is_vertical
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {h : ℝ} (hh : 0 < h)
    (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (line : ℝ → ℂ)
    (hb : ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ flatFullNormalStrip h,
      (F ⟨(q : ℂ), hq⟩).1 = line q)
    (r : ℝ) (x : ℂ) (htop : (F (fullStripPoint r ⟨h, hh.le, le_rfl⟩)).1 = x)
    (gamma : unitInterval → ℂ) (h0 : gamma 0 = line r) (h1 : gamma 1 = x)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (gamma s) (gamma t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y (line r) x).toReal) :
    ∀ t, gamma t = (F (fullStripPoint r
      ⟨t.1 * h, mul_nonneg t.2.1 hh.le, mul_le_of_le_one_left hh.le t.2.2⟩)).1 := by
  let normal : unitInterval → ℂ := fun t ↦ (F (fullStripPoint r
    ⟨t.1 * h, mul_nonneg t.2.1 hh.le, mul_le_of_le_one_left hh.le t.2.2⟩)).1
  have hn0 : normal 0 = line r := by
    have hr : (r : ℂ) ∈ flatFullNormalStrip h := by
      simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hh.le
    simpa [normal, fullStripPoint, flatShearedPoint] using hb r hr
  have hn1 : normal 1 = x := by simpa [normal] using htop
  have hnormal : ∀ s t, (pointSmoothConformalEDist a y (normal s) (normal t)).toReal =
      |t.1 - s.1| * h := by
    intro s t
    rw [hF]
    change dist (flatShearedPoint Complex.I r (s.1 * h)) (flatShearedPoint Complex.I r (t.1 * h)) = _
    rw [flatShearedPoint_dist_transverse (by simp),
      show s.1 * h - t.1 * h = (s.1 - t.1) * h by ring,
      abs_mul, abs_of_pos hh, abs_sub_comm]
  have hL : (pointSmoothConformalEDist a y (line r) x).toReal = h := by
    have he := hnormal 0 1
    simpa only [hn0, hn1, Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero, abs_one, one_mul] using he
  have heq := pointConformal_geodesic_unique ha y (line r) x gamma normal h0 h1 hn0 hn1 hd
    (fun s t ↦ by rw [hnormal, hL])
  exact fun t ↦ congrFun heq t

end RepulsiveCoulomb
