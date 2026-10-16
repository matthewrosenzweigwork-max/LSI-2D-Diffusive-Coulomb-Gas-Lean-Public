import LeanResearch.RepulsiveCoulomb.PointSectorReturnFullInitialSide
import LeanResearch.RepulsiveCoulomb.PointLineCapLocalSide

/-! Isolated, uncompiled successor for genuinely arbitrary original boundary
clocks. A continuous embedded arc with a radial germ fills all sufficiently
small radii by IVT. Compactness then excludes its remote portion. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A genuine ray-valued initial germ determines the entire small-disk arc
trace. No constant-speed or linear radial parametrization is imposed. -/
theorem exists_arc_exact_radial_boundary_of_germ
    (α : unitInterval → ℂ) (hα : Continuous α) (hi : Function.Injective α)
    (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ} (hp : p ∈ e.source)
    (hep : e p = 0) (hα0 : α 0 = p)
    (τ : unitInterval) (hτ : 0 < τ.1) {θ : ℝ}
    (hsource : ∀ t : unitInterval, t ≤ τ → α t ∈ e.source)
    (hgerm : ∀ t : unitInterval, t ≤ τ →
      e (α t) = pointRadialSectorPoint ‖e (α t)‖ θ) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : ℂ) δ ⊆ e.target ∧
      ∀ z ∈ ball (0 : ℂ) δ, e.symm z ∈ range α ↔ z ∈ pointDiskRay δ θ := by
  let K := α '' Ici τ
  have hK : IsCompact K := isClosed_Ici.isCompact.image hα
  have hpK : p ∉ K := by
    rintro ⟨t, ht, he⟩
    have ht0 : t = 0 := hi (he.trans hα0.symm)
    have hval : t.1 = 0 := congrArg Subtype.val ht0
    have hτt : τ.1 ≤ t.1 := ht
    linarith
  have hτchart : e (α τ) ≠ 0 := by
    intro he
    have hατ : α τ = p := e.injOn (hsource τ le_rfl) hp (he.trans hep.symm)
    have ht0 : τ = 0 := hi (hατ.trans hα0.symm)
    have hval : τ.1 = 0 := congrArg Subtype.val ht0
    exact hτ.ne' hval
  have hL : 0 < ‖e (α τ)‖ := norm_pos_iff.mpr hτchart
  let O := e.target ∩ e.symm ⁻¹' Kᶜ
  have hO : IsOpen O := e.isOpen_inter_preimage_symm hK.isClosed.isOpen_compl
  have h0target : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  have hinv : e.symm (0 : ℂ) = p := by rw [← hep, e.left_inv hp]
  have h0O : (0 : ℂ) ∈ O := ⟨h0target, by simpa only [mem_preimage, mem_compl_iff, hinv] using hpK⟩
  obtain ⟨d, hd, hdO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0O)
  let δ := min d ‖e (α τ)‖
  have hδ : 0 < δ := lt_min hd hL
  have hδd : δ ≤ d := min_le_left _ _
  have hδL : δ ≤ ‖e (α τ)‖ := min_le_right _ _
  have hnorm_cont : ContinuousOn (fun t : unitInterval => ‖e (α t)‖) (Icc 0 τ) := by
    apply ContinuousOn.norm
    exact e.continuousOn.comp hα.continuousOn (fun t ht => hsource t ht.2)
  have hnorm0 : ‖e (α 0)‖ = 0 := by rw [hα0, hep, norm_zero]
  have hzeroτ : (0 : unitInterval) ≤ τ := τ.2.1
  refine ⟨δ, hδ, fun z hz => (hdO (ball_subset_ball hδd hz)).1, ?_⟩
  intro z hz
  have hzO := hdO (ball_subset_ball hδd hz)
  have hzt : z ∈ e.target := hzO.1
  have havoid : e.symm z ∉ K := hzO.2
  constructor
  · rintro ⟨t, ht⟩
    have htl : t < τ := by
      by_contra hn
      exact havoid ⟨t, le_of_not_gt hn, ht⟩
    have hchart : e (α t) = z := by rw [ht, e.right_inv hzt]
    have he : pointRadialSectorPoint ‖z‖ θ = z := by
      simpa only [hchart] using (hgerm t htl.le).symm
    refine ⟨‖z‖, ⟨norm_nonneg z, ?_⟩, he⟩
    simpa only [mem_ball, dist_zero_right] using hz
  · rintro ⟨s, hs, he⟩
    have hsI : s ∈ Icc ‖e (α 0)‖ ‖e (α τ)‖ := by
      rw [hnorm0]
      exact ⟨hs.1, hs.2.le.trans hδL⟩
    obtain ⟨t, ht, hnorm⟩ := intermediate_value_Icc hzeroτ hnorm_cont hsI
    change ‖e (α t)‖ = s at hnorm
    refine ⟨t, ?_⟩
    have hchart : e (α t) = z := by
      rw [hgerm t ht.2, hnorm]
      exact he
    rw [← hchart, e.left_inv (hsource t ht.2)]

/-- Exact whole local boundary from two actual radial germs, without changing
or prescribing either original compact arc's clock. -/
theorem exists_twoArc_exact_radial_boundary_of_germs
    (α β : unitInterval → ℂ) (hα : Continuous α) (hβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ} (hp : p ∈ e.source)
    (hep : e p = 0) (hα0 : α 0 = p) (hβ0 : β 0 = p)
    (τL τR : unitInterval) (hτL : 0 < τL.1) (hτR : 0 < τR.1) {θ : ℝ}
    (hsrcL : ∀ t : unitInterval, t ≤ τL → α t ∈ e.source)
    (hsrcR : ∀ t : unitInterval, t ≤ τR → β t ∈ e.source)
    (hleft : ∀ t : unitInterval, t ≤ τL →
      e (α t) = pointRadialSectorPoint ‖e (α t)‖ 0)
    (hright : ∀ t : unitInterval, t ≤ τR →
      e (β t) = pointRadialSectorPoint ‖e (β t)‖ θ) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : ℂ) δ ⊆ e.target ∧
      ∀ z ∈ ball (0 : ℂ) δ,
        e.symm z ∈ range α ∪ range β ↔ z ∈ pointDiskRay δ 0 ∪ pointDiskRay δ θ := by
  obtain ⟨δL, hδL, hballL, hlocalL⟩ := exists_arc_exact_radial_boundary_of_germ
    α hα hiα e hp hep hα0 τL hτL hsrcL hleft
  obtain ⟨δR, hδR, _, hlocalR⟩ := exists_arc_exact_radial_boundary_of_germ
    β hβ hiβ e hp hep hβ0 τR hτR hsrcR hright
  let δ := min δL δR
  have hδ : 0 < δ := lt_min hδL hδR
  have hδLle : δ ≤ δL := min_le_left _ _
  have hδRle : δ ≤ δR := min_le_right _ _
  refine ⟨δ, hδ, fun z hz => hballL (ball_subset_ball hδLle hz), ?_⟩
  intro z hz
  rw [mem_union, hlocalL z (ball_subset_ball hδLle hz),
    hlocalR z (ball_subset_ball hδRle hz)]
  exact or_congr (lineCap_disk_ray_radius_restrict hδLle hz)
    (lineCap_disk_ray_radius_restrict hδRle hz)

/-- Actual stopped-ray and old-boundary arcs supply the cap's full initial
chart directly. In particular no independently parametrized simple loop with
prearranged radial clocks is required. Jordan regions are the actual regions
constructed from these two arcs by first-return topology. -/
theorem exists_sectorReturn_germ_full_initial_chart
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P U V : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hlo : C.lo < 0) (hhi : 0 < C.hi) (hproper : C.hi - C.lo < 2 * Real.pi)
    (α β : unitInterval → ℂ) (hα : Continuous α) (hβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hα0 : α 0 = p) (hβ0 : β 0 = p)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (range α ∪ range β)ᶜ) (hcompact : IsCompact (closure U))
    (hfrontU : frontier U = range α ∪ range β) (hfrontV : frontier V = range α ∪ range β)
    (τL τR : unitInterval) (hτL : 0 < τL.1) (hτR : 0 < τR.1)
    (hsrcL : ∀ t : unitInterval, t ≤ τL → α t ∈ C.chart.source)
    (hsrcR : ∀ t : unitInterval, t ≤ τR → β t ∈ C.chart.source)
    (hleft : ∀ t : unitInterval, t ≤ τL →
      C.chart (α t) = pointRadialSectorPoint ‖C.chart (α t)‖ 0)
    (hright : ∀ t : unitInterval, t ≤ τR →
      C.chart (β t) = pointRadialSectorPoint ‖C.chart (β t)‖ C.hi)
    (ρ : ℝ → ℂ) (hρ : Continuous ρ)
    (hρavoid : ∀ t, 0 < t → ρ t ∉ range α ∪ range β)
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
  have hβfull : C.hi < 2 * Real.pi := by linarith
  obtain ⟨δ, hδ, hδball, hboundary⟩ := exists_twoArc_exact_radial_boundary_of_germs
    α β hα hβ hiα hiβ C.chart hp C.center hα0 hβ0 τL τR hτL hτR
    hsrcL hsrcR hleft hright
  let W := ρ '' Ioi (0 : ℝ)
  have hW : IsPreconnected W := isPreconnected_Ioi.image ρ hρ.continuousOn
  have hWK : Disjoint W (range α ∪ range β) := by
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
    have htδ : t < δ / c₀ :=
      (half_lt_self (lt_min hη (div_pos hδ hc₀))).trans_le (min_le_right _ _)
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
  have hpK : p ∈ range α ∪ range β := Or.inl ⟨0, hα0⟩
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
