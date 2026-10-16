import LeanResearch.RepulsiveCoulomb.PointLineCapEndpointJoinTransport
import LeanResearch.RepulsiveCoulomb.PointLineCapMixedGaussBonnet
import LeanResearch.RepulsiveCoulomb.PointFiniteCornerChosenRotation
import LeanResearch.RepulsiveCoulomb.PointRadialCornerActualSide
import LeanResearch.RepulsiveCoulomb.PointCornerPhysicalChartTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-! Uncompiled records-only successor. Actual finite cap GB data are OUTPUTS
from the original metric line and literal transverse circle crossings. Neither
ordinary join conditions nor orientation/angle/mass identities are inputs. -/
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators Classical
namespace RepulsiveCoulomb

structure PointActualCapGBData {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℝ → ℂ) {R : ℝ}
    (D : LineCapGeometry c R) where
  pieces : List (PointRadialC1ArcPiece ha y (lineCapSegment c D.minus D.plus))
  length_pos : 0 < pieces.length
  curve : ℕ → ℝ → ℂ
  piece_eq : ∀ k (hk : k < pieces.length), curve k = (pieces.get ⟨k, hk⟩).curve
  circle_eq : curve pieces.length = pointCircleCapArc R D.alpha D.beta
  smooth : ∀ k ≤ pieces.length, ContDiff ℝ 1 (curve k)
  consecutive : ∀ k < pieces.length, curve k 1 = curve (k + 1) 0
  closing : curve pieces.length 1 = curve 0 0
  regular : ∀ k ≤ pieces.length, ∀ t ∈ Icc (0 : ℝ) 1, deriv (curve k) t ≠ 0
  simple : ∀ i j, i ≤ pieces.length → j ≤ pieces.length → ∀ s t,
    s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → curve i s = curve j t → i = j ∧ s = t
  carrier : (⋃ k ≤ pieces.length, curve k '' Icc (0 : ℝ) 1) = D.boundary
  avoid : ∀ k ≤ pieces.length, ∀ t ∈ Ioo (0 : ℝ) 1, curve k t ∉ pointPunctures a y
  angle : ℕ → ℝ
  angle_range : ∀ k ≤ pieces.length, 0 < angle k ∧ angle k < 2 * Real.pi
  principal_turn : ∀ k ≤ pieces.length, Complex.arg (deriv (curve k) 0 /
    deriv (curve (if k = 0 then pieces.length else k - 1)) 1) = Real.pi - angle k
  observer : ℂ
  observer_inside : observer ∈ D.inside
  observerAngle : ℕ → Icc (0 : ℝ) 1 → ℝ
  observerAngle_continuous : ∀ k ≤ pieces.length, Continuous (observerAngle k)
  observerAngle_lift : ∀ k ≤ pieces.length, ∀ t,
    Complex.exp ((observerAngle k t : ℂ) * Complex.I) =
      (curve k t - observer) / (‖curve k t - observer‖ : ℂ)
  observerAngle_turn : (∑ k ∈ Finset.range (pieces.length + 1),
    (observerAngle k 1 - observerAngle k 0)) = 2 * Real.pi
  radial_at_positive : ∀ k ≤ pieces.length, 0 < coalescedPointExponent a y (curve k 0) →
    ∃ G : PointFiniteRadialCornerAt curve pieces.length k (angle k),
      ∃ q : ℂ, ‖q‖ = 1 ∧ G.chart.source =
        (pointChosenSmoothRadialChart ha y (curve k 0)).source ∧
        ∀ z, G.chart z = q * pointChosenSmoothRadialChart ha y (curve k 0) z
  gauss_bonnet : pointLineCapCircleTurn a y D +
    (∑ k ∈ Finset.range (pieces.length + 1),
      (Real.pi - (1 + coalescedPointExponent a y (curve k 0) / 2) * angle k)) =
      2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ D.inside then a j / 2 else 0)

/-- This discharges the two join hypotheses of the earlier conditional
consumer from actual crossing radial signs and constructed endpoint clocks. -/
theorem exists_pointActualCapGBData
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R : ℝ} (D : LineCapGeometry c R) (hy : ∀ j, 2 * ‖y j‖ ≤ R)
    (hm : physicalRadialProjection (c D.minus) (deriv c D.minus) < 0)
    (hp : 0 < physicalRadialProjection (c D.plus) (deriv c D.plus)) :
    Nonempty (PointActualCapGBData ha y c D) := by
  obtain ⟨es, hes, hn, hcircle, hpieces, hf, hv, hclose, hreg, hinj, hcarrier⟩ :=
    exists_pointMetricLine_cap_nat_family ha y c hd D.time_lt D.radius_pos D.angle_lt
      D.angle_width D.crosses D.circle_zero D.circle_one
  let f := lineCapNatCurve (es.map (fun e => e.curve) ++ [pointCircleCapArc R D.alpha D.beta])
  have hy' : ∀ j, ‖y j‖ < R := by
    intro j
    have h := hy j
    linarith [D.radius_pos, norm_nonneg (y j)]
  obtain ⟨hjoin0, hjoinN⟩ := pointLineCap_representative_joins_non_cuspidal ha y c hd D hy'
    es f hn hpieces hcircle hv hclose hreg hm hp
  obtain ⟨θ, hθ, hturn, _, hGB⟩ := lineCap_nat_mixed_GB_of_two_join_conditions ha y c hd D hy
    es f hn hpieces hcircle hf hv hclose hreg hinj hcarrier hjoin0 hjoinN
  have hγ := lineCapSegment_injective (pointMetricLine_isClosedEmbedding ha y c hd).injective D.time_lt
  obtain ⟨havoid, hgerms, _⟩ := lineCap_nat_original_germs ha y hγ es f hn hpieces
    D.radius_pos hy' hcircle hv hclose hinj
  have hcover : D.inside ∪ D.outside = (⋃ k ≤ es.length, f k '' Icc (0 : ℝ) 1)ᶜ := by
    rw [hcarrier]
    exact D.cover
  obtain ⟨w, hw, Ξ, hΞ, hΞl, hΞturn⟩ := exists_lineCap_nat_positive_observer_lifts f es.length
    hf hv hclose hinj D.radius_pos D.angle_lt hcircle D.inside_open D.inside_connected
    D.outside_open D.outside_connected D.compact_closure hcover D.inside_ball_and_disjoint.1
  have hrad (k : ℕ) (hk : k ≤ es.length) (hκ : 0 < coalescedPointExponent a y (f k 0)) :
      ∃ G : PointFiniteRadialCornerAt f es.length k (θ k), ∃ q : ℂ, ‖q‖ = 1 ∧
        G.chart.source = (pointChosenSmoothRadialChart ha y (f k 0)).source ∧
        ∀ z, G.chart z = q * pointChosenSmoothRadialChart ha y (f k 0) z := by
    obtain ⟨u, v, hu, hv0, hleft, hright⟩ := hgerms k hk hκ
    obtain ⟨β, G, _, q, hq, hGsrc, hG⟩ := exists_point_finite_radial_corner_with_chosen_rotation
      ha y f es.length hn hv hclose hinj k hk u v hu hv0 hleft hright
    have hβ := G.principal_turn_eq hf
    rw [G.incoming_index_eq hv hclose hinj] at hβ
    have hβθ : β = θ k := by linarith [hturn k hk]
    subst β
    exact ⟨G, q, hq, hGsrc, hG⟩
  exact ⟨⟨es, hn, f, hpieces, hcircle, hf, hv, hclose, hreg, hinj, hcarrier, havoid,
    θ, hθ, hturn, w, hw, Ξ, hΞ, hΞl, hΞturn, hrad, hGB⟩⟩

/-- Every positive vertex carries an actual full positive-side interval AND
an actual classical-cone transition from the very same chosen smooth chart.
These are constructed geometric witnesses, not inferred mass coefficients. -/
theorem PointActualCapGBData.positive_vertex_physical_side
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ} {R : ℝ} {D : LineCapGeometry c R}
    (H : PointActualCapGBData ha y c D) {k : ℕ} (hk : k ≤ H.pieces.length)
    (hκ : 0 < coalescedPointExponent a y (H.curve k 0)) :
    ∃ E F : OpenPartialHomeomorph ℂ ℂ, ∃ δ : ℝ,
      0 < δ ∧ ball (0 : ℂ) δ ⊆ E.target ∧
      (∀ z ∈ ball (0 : ℂ) δ, E.symm z ∈ closure D.inside ↔
        z ∈ lineClosedInitialSector δ (H.angle k)) ∧
      (∀ z ∈ ball (0 : ℂ) δ, E.symm z ∈ closure D.outside ↔
        z ∈ lineClosedTerminalSector δ (H.angle k)) ∧
      H.curve k 0 ∈ F.source ∧ F (H.curve k 0) = 0 ∧ F.source ⊆ E.source ∧
      (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y (H.curve k 0) / 2)
        (div_nonneg (coalescedPointExponent_nonneg a y (H.curve k 0)) (by norm_num)) (E z)) ∧
      (∀ u ∈ F.source, ∀ v ∈ F.source,
        (pointSmoothConformalEDist a y u v).toReal =
          pointClassicalConeDist a y (H.curve k 0) (F u) (F v)) := by
  obtain ⟨G, q, hq, hGsrc, hG⟩ := H.radial_at_positive k hk hκ
  have hcover : D.inside ∪ D.outside = (⋃ i ≤ H.pieces.length, H.curve i '' Icc (0 : ℝ) 1)ᶜ := by
    rw [H.carrier]
    exact D.cover
  have hpC : H.curve k 0 ∈ D.boundary := by
    rw [← H.carrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨0, by norm_num, rfl⟩⟩⟩
  obtain ⟨δ, hδ, hball, hboundary, hinside, houtside⟩ := G.actual_full_inside_sector
    (fun i hi => (H.smooth i hi).continuous) H.simple D.inside_open D.inside_connected
    D.outside_open D.outside_connected D.disjoint D.compact_closure hcover
    (frontier_subset_closure (D.frontier_inside.symm ▸ hpC))
    (frontier_subset_closure (D.frontier_outside.symm ▸ hpC)) H.observer_inside H.observerAngle
    H.observerAngle_continuous (fun i hi t _ => H.observerAngle_lift i hi t) H.observerAngle_turn
  have hfrontU : frontier D.inside = ⋃ i ≤ H.pieces.length, H.curve i '' Icc (0 : ℝ) 1 := by
    rw [H.carrier]
    exact D.frontier_inside
  have hfrontV : frontier D.outside = ⋃ i ≤ H.pieces.length, H.curve i '' Icc (0 : ℝ) 1 := by
    rw [H.carrier]
    exact D.frontier_outside
  have hpart := pointDiskRay_complement_eq_sectors hδ G.angle_pos G.angle_lt
  have hpart' : ball (0 : ℂ) δ \ (pointDiskRay δ 0 ∪ pointDiskRay δ (H.angle k)) =
      pointOpenRadialSector δ (H.angle k) (2 * Real.pi) ∪ pointOpenRadialSector δ 0 (H.angle k) := by
    simpa only [union_comm] using hpart
  obtain ⟨F, hpF, hF0, hFsrc, hF, hmetric, _⟩ :=
    exists_pointCorner_physical_metric_transition ha y G.chart hq hGsrc hG
  exact ⟨G.chart, F, δ, hδ, hball,
    fun z hz => chart_closed_side_membership D.disjoint hcover hfrontU G.chart hboundary hpart hinside houtside z hz,
    fun z hz => chart_closed_side_membership D.disjoint.symm (by simpa only [union_comm] using hcover)
      hfrontV G.chart hboundary hpart' houtside hinside z hz,
    hpF, hF0, hFsrc, hF, hmetric⟩

end RepulsiveCoulomb
