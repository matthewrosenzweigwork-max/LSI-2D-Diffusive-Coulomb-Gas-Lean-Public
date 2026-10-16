module

public import LeanResearch.RepulsiveCoulomb.PointSectorReturnCleanRay
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualCleanGerm
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualEdgeGerm
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnOrderedCapChart
public import LeanResearch.RepulsiveCoulomb.PointRetainedConeRotationTransport

@[expose] public section

/-! Isolated, uncompiled actual two-orientation initial-angle construction.
The clean endpoint and opposite old-arc germ are constructed from the same
actual clean ray. Both possible endpoint labels are handled by actual chart
rotations and, in the upper case, swapping the two original compact arcs. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_sectorReturn_actual_both_endpoint_cap_angle
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P U V : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hP : IsClosed P) (hadm : C.Admissible)
    (E : PointGeodesicTreeEdge a y) (hE0 : E.start = p) (hEP : ∀ u, E.curve u ∈ P)
    (hφopen : C.actualInitialRawAngle ha y hadm E hE0 hEP ∈ Ioo C.lo C.hi)
    (β : unitInterval → ℂ) (hβ : Continuous β) (hiβ : Function.Injective β)
    (hβ0 : β 0 = p) (hβfront : ∀ u, β u ∈ frontier P)
    (ρ : ℝ → ℂ) (hρ : Continuous ρ) (hρ0 : ρ 0 = p)
    (hρd : ∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρfront : ∀ t ∈ Ici (0 : ℝ), ρ t ∈ frontier P)
    (hρavoid : ∀ t : ℝ, 0 < t → ρ t ∉ range E.curve ∪ range β)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (range E.curve ∪ range β)ᶜ) (hcompact : IsCompact (closure U))
    (hfrontU : frontier U = range E.curve ∪ range β)
    (hfrontV : frontier V = range E.curve ∪ range β) :
    ∃ ξ : ℝ, ξ ∈ Icc C.lo C.hi ∧ (ξ = C.lo ∨ ξ = C.hi) ∧
      ∃ ε : ℝ, 0 < ε ∧
        (∀ t ∈ Ioo (0 : ℝ) ε, C.chart (ρ t) = pointRadialSectorPoint t ξ) ∧
      ∃ D : PointRetainedConeNeighborhood a y (closure U) p,
        (1 + coalescedPointExponent a y p / 2) * (D.hi - D.lo) =
          (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo) -
            (1 + coalescedPointExponent a y p / 2) *
              |C.actualInitialRawAngle ha y hadm E hE0 hEP - ξ| := by
  let φ := C.actualInitialRawAngle ha y hadm E hE0 hEP
  have hiE : Function.Injective E.curve :=
    pointConformal_geodesic_injective ha y E.distinct E.curve E.geodesic
  have hEcurve0 : E.curve 0 = p := E.curve_start.trans hE0
  obtain ⟨τE, hτE, hsrcE, hgermE⟩ := C.actual_initial_raw_angle_germ ha y hadm E hE0 hEP
  obtain ⟨T, ξ, hT, hTR, hξ, hξend, hclean⟩ :=
    exists_clean_metric_ray_retained_endpoint_germ C hP ρ hρ0 hρd hρfront
  have hcleanInv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      ρ t = C.chart.symm (pointRadialSectorPoint t ξ) := (hclean t ⟨ht.1.le, ht.2.le⟩).2.2
  obtain ⟨τB, hτB, hsrcB, holdgerm⟩ := exists_sectorReturn_opposite_old_boundary_germ
    C hP β hβ hiβ hβ0 hβfront ρ hT hξend hcleanInv
    (fun t ht hmem => hρavoid t ht (Or.inr hmem))
  have hescape := pointMetricRay_positive_escape ha y ρ hρd
  have hproper := C.admissible_coordinate_width_lt_two_pi hadm
  have hcleanTarget (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      pointRadialSectorPoint t ξ ∈ C.chart.target := by
    have hc := hclean t ⟨ht.1.le, ht.2.le⟩
    rw [← hc.2.1]
    exact C.chart.mapsTo hc.1
  refine ⟨ξ, hξ, hξend, T, hT,
    (fun t ht => (hclean t ⟨ht.1.le, ht.2.le⟩).2.1), ?_⟩
  rcases holdgerm with ⟨hξlo, hgermB⟩ | ⟨hξhi, hgermB⟩
  · obtain ⟨R, _, hRsrc, hRF, _, _⟩ := C.exists_rotate φ
    have hsrcE' : ∀ t : unitInterval, t ≤ τE → E.curve t ∈ R.chart.source := by
      intro t ht; rw [hRsrc]; exact hsrcE t ht
    have hsrcB' : ∀ t : unitInterval, t ≤ τB → β t ∈ R.chart.source := by
      intro t ht; rw [hRsrc]; exact hsrcB t ht
    have hnew : ∀ t : unitInterval, t ≤ τE →
        R.chart (E.curve t) = pointRadialSectorPoint ‖R.chart (E.curve t)‖ 0 := by
      intro t ht
      simpa only [φ, sub_self] using sectorReturn_rotated_chart_radial_germ C.chart R.chart hRF (hgermE t ht)
    have hold : ∀ t : unitInterval, t ≤ τB →
        R.chart (β t) = pointRadialSectorPoint ‖R.chart (β t)‖ (C.hi - φ) := by
      intro t ht
      exact sectorReturn_rotated_chart_radial_germ C.chart R.chart hRF (hgermB t ht)
    have hclean' : ∀ t ∈ Ioo (0 : ℝ) T,
        ρ t = R.chart.symm (pointRadialSectorPoint (1 * t) (C.lo - φ + 2 * Real.pi)) := by
      intro t ht
      have hi := sectorReturn_rotated_chart_inverse_radial C.chart R.chart hRsrc hRF (hcleanTarget t ht)
      rw [hξlo] at hi
      rw [one_mul]
      have hp : pointRadialSectorPoint t (C.lo - φ + 2 * Real.pi) =
          pointRadialSectorPoint t (C.lo - φ) := by
        simp only [pointRadialSectorPoint, Circle.exp_add_two_pi]
      rw [hp, hi]
      simpa only [hξlo] using hcleanInv t ht
    obtain ⟨D, _, hDlo, hDhi⟩ := exists_sectorReturn_ordered_actual_cap_chart R
      (show 0 < C.hi - φ by exact sub_pos.mpr hφopen.2)
      (show C.hi - φ < 2 * Real.pi by dsimp [φ] at *; linarith [hφopen.1])
      (show C.lo - φ + 2 * Real.pi ∈ Ioo (C.hi - φ) (2 * Real.pi) by
        constructor <;> dsimp [φ] at * <;> linarith [hφopen.1])
      E.curve β E.continuous hβ hiE hiβ hEcurve0 hβ0 hU hV hUV hcover hcompact hfrontU hfrontV
      τE τB hτE hτB hsrcE' hsrcB' hnew hold ρ hρ hρavoid hescape hT
      (by norm_num : (0 : ℝ) < 1) hclean'
    refine ⟨D, ?_⟩
    rw [hDlo, hDhi, hξlo, abs_of_nonneg (sub_nonneg.mpr hφopen.1.le)]
    dsimp [φ]
    ring
  · obtain ⟨R, _, hRsrc, hRF, _, _⟩ := C.exists_rotate C.lo
    have hsrcE' : ∀ t : unitInterval, t ≤ τE → E.curve t ∈ R.chart.source := by
      intro t ht; rw [hRsrc]; exact hsrcE t ht
    have hsrcB' : ∀ t : unitInterval, t ≤ τB → β t ∈ R.chart.source := by
      intro t ht; rw [hRsrc]; exact hsrcB t ht
    have hold : ∀ t : unitInterval, t ≤ τB →
        R.chart (β t) = pointRadialSectorPoint ‖R.chart (β t)‖ 0 := by
      intro t ht
      simpa only [sub_self] using sectorReturn_rotated_chart_radial_germ C.chart R.chart hRF (hgermB t ht)
    have hnew : ∀ t : unitInterval, t ≤ τE →
        R.chart (E.curve t) = pointRadialSectorPoint ‖R.chart (E.curve t)‖ (φ - C.lo) := by
      intro t ht
      exact sectorReturn_rotated_chart_radial_germ C.chart R.chart hRF (hgermE t ht)
    have hclean' : ∀ t ∈ Ioo (0 : ℝ) T,
        ρ t = R.chart.symm (pointRadialSectorPoint (1 * t) (C.hi - C.lo)) := by
      intro t ht
      have hi := sectorReturn_rotated_chart_inverse_radial C.chart R.chart hRsrc hRF (hcleanTarget t ht)
      rw [hξhi] at hi
      rw [one_mul, hi]
      simpa only [hξhi] using hcleanInv t ht
    have hcover' : U ∪ V = (range β ∪ range E.curve)ᶜ := by simpa only [union_comm] using hcover
    have hfrontU' : frontier U = range β ∪ range E.curve := by simpa only [union_comm] using hfrontU
    have hfrontV' : frontier V = range β ∪ range E.curve := by simpa only [union_comm] using hfrontV
    obtain ⟨D, _, hDlo, hDhi⟩ := exists_sectorReturn_ordered_actual_cap_chart R
      (show 0 < φ - C.lo by exact sub_pos.mpr hφopen.1)
      (show φ - C.lo < 2 * Real.pi by dsimp [φ] at *; linarith [hφopen.2])
      (show C.hi - C.lo ∈ Ioo (φ - C.lo) (2 * Real.pi) by
        constructor <;> dsimp [φ] at * <;> linarith [hφopen.2])
      β E.curve hβ E.continuous hiβ hiE hβ0 hEcurve0 hU hV hUV hcover' hcompact hfrontU' hfrontV'
      τB τE hτB hτE hsrcB' hsrcE' hold hnew ρ hρ
      (by intro t ht h; exact hρavoid t ht (by simpa only [union_comm] using h))
      hescape hT (by norm_num : (0 : ℝ) < 1) hclean'
    refine ⟨D, ?_⟩
    rw [hDlo, hDhi, hξhi, abs_of_nonpos (sub_nonpos.mpr hφopen.2.le), neg_sub]
    dsimp [φ]
    ring

end RepulsiveCoulomb
