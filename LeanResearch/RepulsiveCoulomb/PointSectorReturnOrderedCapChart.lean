module

public import LeanResearch.RepulsiveCoulomb.PointSectorReturnUnclockedBoundary

@[expose] public section

/-! Isolated, uncompiled orientation-neutral side constructor. Two actual
boundary germs are at 0 and omega; the actual escaping old germ lies strictly
in their complementary sector. Their full physical widths are not truncated. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_sectorReturn_ordered_actual_cap_chart
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P U V : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    {ω ξ : ℝ} (hω : 0 < ω) (hωfull : ω < 2 * Real.pi)
    (hξ : ξ ∈ Ioo ω (2 * Real.pi))
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
      C.chart (β t) = pointRadialSectorPoint ‖C.chart (β t)‖ ω)
    (ρ : ℝ → ℂ) (hρ : Continuous ρ)
    (hρavoid : ∀ t, 0 < t → ρ t ∉ range α ∪ range β)
    (hρescape : ∀ A : Set ℂ, IsCompact A → ∃ t, 0 < t ∧ ρ t ∉ A)
    {η c₀ : ℝ} (hη : 0 < η) (hc₀ : 0 < c₀)
    (hρgerm : ∀ t ∈ Ioo (0 : ℝ) η,
      ρ t = C.chart.symm (pointRadialSectorPoint (c₀ * t) ξ)) :
    ∃ D : PointRetainedConeNeighborhood a y (closure U) p,
      D.chart = C.chart ∧ D.lo = 0 ∧ D.hi = ω := by
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hp := C.source hpp
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
  have hselector : ∃ z ∈ pointOpenRadialSector δ ω (2 * Real.pi), C.chart.symm z ∈ W := by
    let t := min η (δ / c₀) / 2
    have ht : 0 < t := half_pos (lt_min hη (div_pos hδ hc₀))
    have htη : t < η := by dsimp [t]; linarith [min_le_left η (δ / c₀)]
    have htδ : t < δ / c₀ :=
      (half_lt_self (lt_min hη (div_pos hδ hc₀))).trans_le (min_le_right _ _)
    have hrad : c₀ * t ∈ Ioo (0 : ℝ) δ :=
      ⟨mul_pos hc₀ ht, by nlinarith [(lt_div_iff₀ hc₀).mp htδ]⟩
    refine ⟨pointRadialSectorPoint (c₀ * t) ξ,
      ⟨(c₀ * t, ξ), ⟨hrad, hξ⟩, rfl⟩, ?_⟩
    rw [← hρgerm t ⟨ht, htη⟩]
    exact ⟨t, ht, rfl⟩
  have hpK : p ∈ range α ∪ range β := Or.inl ⟨0, hα0⟩
  have hpU : p ∈ closure U := frontier_subset_closure (hfrontU.symm ▸ hpK)
  have hpV : p ∈ closure V := frontier_subset_closure (hfrontV.symm ▸ hpK)
  have hside := pointRadialChart_initial_side_of_escaping_selector
    hU hV hUV hcover hcompact hW hWK hescape hpU hpV C.chart hp C.center
    hδ hω hωfull hδball hboundary hselector
  have hclosed : ∀ z ∈ ball (0 : ℂ) δ,
      C.chart.symm z ∈ closure U ↔ z ∈ lineClosedInitialSector δ ω := by
    exact chart_closed_side_membership hUV hcover hfrontU C.chart hboundary
      (pointDiskRay_complement_eq_sectors hδ hω hωfull) hside.1 hside.2
  exact C.exists_actual_initial_side_chart hδ hω hωfull hclosed

end RepulsiveCoulomb
