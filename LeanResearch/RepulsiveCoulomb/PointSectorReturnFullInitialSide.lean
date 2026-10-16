import LeanResearch.RepulsiveCoulomb.PlanarFirstReturnJordanCaps
import LeanResearch.RepulsiveCoulomb.PointRadialLoopBoundary
import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfConeSides
import LeanResearch.RepulsiveCoulomb.PointLineFullIntervalWidth
import LeanResearch.RepulsiveCoulomb.PointRetainedWidthInvariance

/-! Isolated, uncompiled sector-return successor. The actual full local cap
side is selected by a connected escaping OLD ray. The input consists of actual
radial collars and a genuine retained metric chart. No occupied sector, cap
angle identity, principal-angle bound, or zero ambient exponent is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A connected escaping set selects the exterior of a Jordan curve. A point
of its actual germ in the terminal polar sector selects the entire OTHER sector
as the bounded side. This preserves the whole topological angular interval. -/
theorem pointRadialChart_initial_side_of_escaping_selector
    {K U V W : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Kᶜ) (hcompact : IsCompact (closure U))
    (hW : IsPreconnected W) (hWK : Disjoint W K)
    (hescape : ∀ A : Set ℂ, IsCompact A → ∃ x ∈ W, x ∉ A)
    {p : ℂ} (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (e : OpenPartialHomeomorph ℂ ℂ) (hp : p ∈ e.source) (hep : e p = 0)
    {R β : ℝ} (hR : 0 < R) (hβ : 0 < β) (hβfull : β < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hboundary : ∀ z ∈ ball (0 : ℂ) R,
      e.symm z ∈ K ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R β)
    (hselector : ∃ z ∈ pointOpenRadialSector R β (2 * Real.pi), e.symm z ∈ W) :
    MapsTo e.symm (pointOpenRadialSector R 0 β) U ∧
      MapsTo e.symm (pointOpenRadialSector R β (2 * Real.pi)) V := by
  have hout := connected_escaping_set_outside_bounded_jordan_region
    hU hV hUV hcover hcompact hW hWK hescape
  rcases pointRadialChart_region_side_choice hU hV hUV hcover hpU hpV
    e hp hep hR hβ hβfull hball hboundary with hside | hside
  · exact hside
  · obtain ⟨z, hz, hzW⟩ := hselector
    exact False.elim (disjoint_left.mp hUV (hside.2 hz) (hout.1 hzW))

/-- Radial-sector membership with a smaller closed radius is obtained from
literal side membership and a norm bound; the angular interval is unchanged. -/
theorem sectorReturn_closed_initial_iff_retained_interval
    {z : ℂ} {R S β : ℝ} (hz : z ∈ ball (0 : ℂ) R)
    (hzS : ‖z‖ ≤ S) (hβ : 0 < β) :
    z ∈ lineClosedInitialSector R β ↔ z ∈ pointClosedRadialInterval S 0 β := by
  constructor
  · rintro ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩)
    · refine ⟨r, ⟨hr.1, ?_⟩, 0, ⟨le_rfl, hβ.le⟩, rfl⟩
      simpa only [pointRadialSectorPoint_norm hr.1] using hzS
    · refine ⟨r, ⟨hr.1, ?_⟩, β, ⟨hβ.le, le_rfl⟩, rfl⟩
      simpa only [pointRadialSectorPoint_norm hr.1] using hzS
    · refine ⟨r, ⟨hr.1.le, ?_⟩, φ, ⟨hφ.1.le, hφ.2.le⟩, rfl⟩
      simpa only [pointRadialSectorPoint_norm hr.1.le] using hzS
  · rintro ⟨r, hr, φ, hφ, rfl⟩
    have hrR : r < R := by
      simpa only [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.1] using hz
    by_cases hφ0 : φ = 0
    · exact Or.inl (Or.inl ⟨r, ⟨hr.1, hrR⟩, by rw [hφ0]⟩)
    by_cases hφβ : φ = β
    · exact Or.inl (Or.inr ⟨r, ⟨hr.1, hrR⟩, by rw [hφβ]⟩)
    by_cases hr0 : r = 0
    · exact Or.inl (Or.inl ⟨0, ⟨le_rfl, by linarith⟩,
        by simp only [hr0, pointRadialSectorPoint_zero]⟩)
    · exact Or.inr ⟨(r, φ), ⟨⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hrR⟩,
        ⟨lt_of_le_of_ne hφ.1 (Ne.symm hφ0), lt_of_le_of_ne hφ.2 hφβ⟩⟩, rfl⟩

/-- Build an actual retained cap chart by restricting the SAME full ambient
metric chart, once topology has established its literal local closed side.
The smaller metric disk and its onto property are outputs. -/
theorem PointRetainedConeNeighborhood.exists_actual_initial_side_chart
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    {δ β : ℝ} (hδ : 0 < δ) (hβ : 0 < β) (hβfull : β < 2 * Real.pi)
    (hside : ∀ z ∈ ball (0 : ℂ) δ,
      C.chart.symm z ∈ Q ↔ z ∈ lineClosedInitialSector δ β) :
    ∃ D : PointRetainedConeNeighborhood a y Q p,
      D.chart = C.chart ∧ D.lo = 0 ∧ D.hi = β := by
  let R := min C.radius δ / 2
  have hR : 0 < R := half_pos (lt_min C.radius_pos hδ)
  have hRC : R ≤ C.radius := by
    dsimp [R]
    linarith [min_le_left C.radius δ, lt_min C.radius_pos hδ]
  have hRδ : R < δ := by
    dsimp [R]
    linarith [min_le_right C.radius δ, lt_min C.radius_pos hδ]
  have hnorm (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ R) :
      ‖C.chart z‖ = (pointSmoothConformalEDist a y z p).toReal :=
    C.retainedWidth_chart_norm (hz.trans hRC)
  have honto : BijOn C.chart
      {z : ℂ | (pointSmoothConformalEDist a y z p).toReal ≤ R}
      {z : ℂ | ‖z‖ ≤ R} := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      change ‖C.chart z‖ ≤ R
      rwa [hnorm z hz]
    · intro z hz w hw he
      exact C.onto.injOn (hz.trans hRC) (hw.trans hRC) he
    · intro z hz
      obtain ⟨ht, he, hd⟩ := C.retainedWidth_inverse (hz.trans hRC)
      exact ⟨C.chart.symm z, hd.trans_le hz, he⟩
  let D : PointRetainedConeNeighborhood a y Q p :=
    { chart := C.chart
      radius := R
      radius_pos := hR
      center := C.center
      source := fun z hz => C.source (hz.trans hRC)
      onto := honto
      metric := fun z hz w hw => C.metric z (hz.trans hRC) w (hw.trans hRC)
      lo := 0
      hi := β
      width_pos := hβ
      width_le_full := by simpa only [sub_zero] using hβfull.le
      retained := by
        intro z hz
        have hzsource := C.source (hz.trans hRC)
        have hznorm : ‖C.chart z‖ ≤ R := (hnorm z hz).trans_le hz
        have hzball : C.chart z ∈ ball (0 : ℂ) δ := by
          rw [mem_ball, dist_zero_right]
          exact hznorm.trans_lt hRδ
        have hm : z ∈ Q ↔ C.chart z ∈ lineClosedInitialSector δ β := by
          simpa only [C.chart.left_inv hzsource] using hside (C.chart z) hzball
        exact hm.trans (sectorReturn_closed_initial_iff_retained_interval hzball hznorm hβ) }
  exact ⟨D, rfl, rfl, rfl⟩

/-- Starting with actual simple-loop collars in the old retained metric chart,
construct the whole local cap side. The clean ray has its ordered old endpoint
at C.lo < 0; its equivalent representative C.lo + 2*pi lies in the complementary
sector, since the OLD retained interval is proper. Physical widths may exceed pi. -/
theorem exists_sectorReturn_actual_full_initial_chart
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P U V : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hlo : C.lo < 0) (hhi : 0 < C.hi) (hproper : C.hi - C.lo < 2 * Real.pi)
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ)
    (hinj : InjOn γ {t : Icc (0 : ℝ) 1 | t.1 < 1}) (hγ0 : γ 0 = p)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (range γ)ᶜ) (hcompact : IsCompact (closure U))
    (hfrontU : frontier U = range γ) (hfrontV : frontier V = range γ)
    {l r cL cR : ℝ} (hl : 0 < l) (hlr : l < r) (hr : r < 1)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (hLrad : cL * l < C.radius) (hRrad : cR * (1 - r) < C.radius)
    (hleft : ∀ t : Icc (0 : ℝ) 1, t.1 ≤ l →
      γ t = C.chart.symm (pointRadialSectorPoint (cL * t.1) 0))
    (hright : ∀ t : Icc (0 : ℝ) 1, r ≤ t.1 →
      γ t = C.chart.symm (pointRadialSectorPoint (cR * (1 - t.1)) C.hi))
    (ρ : ℝ → ℂ) (hρ : Continuous ρ)
    (hρavoid : ∀ t, 0 < t → ρ t ∉ range γ)
    (hρescape : ∀ A : Set ℂ, IsCompact A → ∃ t, 0 < t ∧ ρ t ∉ A)
    {η c₀ : ℝ} (hη : 0 < η) (hc₀ : 0 < c₀)
    (hρgerm : ∀ t ∈ Ioo (0 : ℝ) η,
      ρ t = C.chart.symm (pointRadialSectorPoint (c₀ * t) C.lo)) :
    ∃ D : PointRetainedConeNeighborhood a y (closure U) p,
      D.chart = C.chart ∧ D.lo = 0 ∧ D.hi = C.hi ∧
      (1 + coalescedPointExponent a y p / 2) * (D.hi - D.lo) =
        (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo) -
          (1 + coalescedPointExponent a y p / 2) * (-C.lo) := by
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hp := C.source hpp
  have hball : ball (0 : ℂ) C.radius ⊆ C.chart.target := by
    intro z hz
    have hznorm : ‖z‖ < C.radius := by
      simpa only [mem_ball, dist_zero_right] using hz
    exact (C.retainedWidth_inverse hznorm.le).1
  have hβfull : C.hi < 2 * Real.pi := by linarith
  obtain ⟨δ, hδ, hδball, hboundary⟩ := exists_simple_loop_exact_radial_boundary
    γ hγ hinj C.chart hp C.center hγ0 hl hlr hr hcL hcR C.radius_pos
    hball hLrad hRrad hleft hright
  let W := ρ '' Ioi (0 : ℝ)
  have hW : IsPreconnected W := isPreconnected_Ioi.image ρ hρ.continuousOn
  have hWK : Disjoint W (range γ) := by
    apply disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hx
    exact hρavoid t ht hx
  have hescape : ∀ A : Set ℂ, IsCompact A → ∃ x ∈ W, x ∉ A := by
    intro A hA
    obtain ⟨t, ht, hnot⟩ := hρescape A hA
    exact ⟨ρ t, ⟨t, ht, rfl⟩, hnot⟩
  have hselector : ∃ z ∈ pointOpenRadialSector δ C.hi (2 * Real.pi), C.chart.symm z ∈ W := by
    let t := min η (δ / c₀) / 2
    have ht : 0 < t := half_pos (lt_min hη (div_pos hδ hc₀))
    have htη : t < η := by dsimp [t]; linarith [min_le_left η (δ / c₀)]
    have htδ : t < δ / c₀ := by
      dsimp [t]
      linarith [min_le_right η (δ / c₀), div_pos hδ hc₀]
    have hrad : c₀ * t ∈ Ioo (0 : ℝ) δ :=
      ⟨mul_pos hc₀ ht, by nlinarith [(lt_div_iff₀ hc₀).mp htδ]⟩
    have hangle : C.lo + 2 * Real.pi ∈ Ioo C.hi (2 * Real.pi) := by
      constructor <;> linarith
    refine ⟨pointRadialSectorPoint (c₀ * t) (C.lo + 2 * Real.pi),
      ⟨(c₀ * t, C.lo + 2 * Real.pi), ⟨hrad, hangle⟩, rfl⟩, ?_⟩
    have hperiod : pointRadialSectorPoint (c₀ * t) (C.lo + 2 * Real.pi) =
        pointRadialSectorPoint (c₀ * t) C.lo := by
      simp only [pointRadialSectorPoint, Circle.exp_add_two_pi]
    rw [hperiod, ← hρgerm t ⟨ht, htη⟩]
    exact ⟨t, ht, rfl⟩
  have hpK : p ∈ range γ := ⟨0, hγ0⟩
  have hpU : p ∈ closure U := frontier_subset_closure (hfrontU.symm ▸ hpK)
  have hpV : p ∈ closure V := frontier_subset_closure (hfrontV.symm ▸ hpK)
  have hside := pointRadialChart_initial_side_of_escaping_selector
    hU hV hUV hcover hcompact hW hWK hescape hpU hpV C.chart hp C.center
    hδ hhi hβfull hδball hboundary hselector
  have hclosed : ∀ z ∈ ball (0 : ℂ) δ,
      C.chart.symm z ∈ closure U ↔ z ∈ lineClosedInitialSector δ C.hi := by
    exact chart_closed_side_membership hUV hcover hfrontU C.chart hboundary
      (pointDiskRay_complement_eq_sectors hδ hhi hβfull) hside.1 hside.2
  obtain ⟨D, hDchart, hDlo, hDhi⟩ :=
    C.exists_actual_initial_side_chart hδ hhi hβfull hclosed
  refine ⟨D, hDchart, hDlo, hDhi, ?_⟩
  rw [hDlo, hDhi]
  ring

end RepulsiveCoulomb
