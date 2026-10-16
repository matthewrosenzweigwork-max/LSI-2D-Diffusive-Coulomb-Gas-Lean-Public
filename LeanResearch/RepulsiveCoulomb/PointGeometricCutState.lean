module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripStateAdapters
public import LeanResearch.RepulsiveCoulomb.PointActualRetainedApexIteration
public import LeanResearch.RepulsiveCoulomb.PointActualFirstMarkedSector
public import LeanResearch.RepulsiveCoulomb.PointCutOuterRank

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The current state contains only genuine original
halfplane geometry, all-point finite coefficients, the scalar invariant, and
an actual finite geodesic frontier cover. It contains no future moves, sector
family, termination witness, global deformation, or angle-allocation answer.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

structure PointGeometricCutState {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (ν α : ℂ →₀ ℝ) extends PointRetainedSignedHalfplaneState a y P ν α where
  budget : PointSignedBudgetInvariant ν α
  pieceCount : ℕ
  pieces : Fin pieceCount → PointClosedBoundaryGeodesicPiece a y
  boundary_cover : frontier P = ⋃ i, range (pieces i).curve

namespace PointGeometricCutState
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}

/-- Packaging the same original supplied-sector premises. Connectedness and
interior charts are derived; they are not new requirements on the user input. -/
def ofOriginal (ha : ∀ j, 0 ≤ a j)
    (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hνoff : ∀ x, x ∉ P → ν x = 0)
    (hνint : ∀ x ∈ interior P, ν x = -Real.pi * coalescedPointExponent a y x)
    (hνboundary : ∀ x ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P x,
      ν x = Real.pi - C.flatPhysicalWidth ∧ C.Admissible)
    (hαP : ∀ x, α x ≠ 0 → x ∈ P) (hbudget : PointSignedBudgetInvariant ν α)
    {N : ℕ} (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve) :
    PointGeometricCutState a y P ν α := by
  have hconnected : IsConnected P := by
    obtain ⟨_, _, hc, _, _, _, hcl, _, _, _⟩ := planar_halfplane_partition
    have hupper : IsConnected planarClosedUpperHalfplane := hcl ▸ hc.closure
    rw [hHP]
    exact H.isConnected_preimage.mpr hupper
  have hcharts : ∀ x ∈ P, ∃ C : PointRetainedConeNeighborhood a y P x,
      C.Full ∨ C.Admissible := by
    intro x hx
    by_cases hi : x ∈ interior P
    · obtain ⟨C, hC⟩ := pointRetainedSector_construct_full_interior_chart ha y hi
      exact ⟨C, Or.inl hC⟩
    · obtain ⟨C, _, hC⟩ := hνboundary x ⟨subset_closure hx, hi⟩
      exact ⟨C, Or.inr hC⟩
  exact {
    ambient := H
    region_eq := hHP
    connected := hconnected
    charts := hcharts
    interior_coeff := hνint
    boundary_coeff := fun x hx ↦ by
      obtain ⟨C, he, hC⟩ := hνboundary x hx
      exact ⟨C, hC, he⟩
    exterior_coeff := hνoff
    allocation_support := hαP
    budget := hbudget
    pieceCount := N
    pieces := pieces
    boundary_cover := hpieces }

theorem interior_marked (K : PointGeometricCutState a y P ν α)
    (x : ℂ) (hx : x ∈ interior P) (he : coalescedPointExponent a y x ≠ 0) :
    x ∈ pointSignedMarked ν α := by
  apply (mem_pointSignedMarked ν α x).mpr
  left
  rw [K.interior_coeff x hx]
  exact mul_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero) he

theorem boundary_formula (K : PointGeometricCutState a y P ν α)
    (x : ℂ) (hx : x ∈ frontier P) :
    ∃ C : PointRetainedConeNeighborhood a y P x,
      ν x = Real.pi - (1 + coalescedPointExponent a y x / 2) * (C.hi - C.lo) := by
  obtain ⟨C, _, he⟩ := K.boundary_coeff x hx
  refine ⟨C, ?_⟩
  simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
    add_comm (coalescedPointExponent a y x / 2) 1] using he

/-- A clean boundary ray is current geometric data, not a future existence
oracle. The full-line producer constructs this; the marked-boundary producer
is the still-open prerequisite documented in the handoff. -/
structure CleanRay (K : PointGeometricCutState a y P ν α) where
  ray : NNReal → ℂ
  metric : ∀ s t, (pointSmoothConformalEDist a y (ray s) (ray t)).toReal = dist s t
  frontier : ∀ t, ray t ∈ _root_.frontier P
  clean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ray 0}) (range ray)
  budget_supported : ray 0 ∈ α.support

end PointGeometricCutState

/-- Output of the actual finite-direction construction, normalized precisely
to the inputs of both actual sector-removal APIs. The fields are not supplied
as extra original-input assumptions. -/
structure PointConstructedCutSector {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (ν α : ℂ →₀ ℝ) where
  beta : ℝ
  positive : 0 < beta
  le_pi : beta ≤ Real.pi
  map : closedEuclideanSector beta → ℂ
  metric : ∀ x z, (pointSmoothConformalEDist a y (map x) (map z)).toReal = dist x z
  mem_region : ∀ x, map x ∈ P
  bottom_frontier : ∀ t : NNReal, map (retainedApexBottomSource positive.le le_pi t) ∈ frontier P
  le_budget : beta ≤ α (map (flatLinkSectorApex positive.le))
  apex_supported : map (flatLinkSectorApex positive.le) ∈ α.support
  chart : PointRetainedConeNeighborhood a y P (map (flatLinkSectorApex positive.le))
  admissible : chart.Admissible
  chart_coeff : ν (map (flatLinkSectorApex positive.le)) = Real.pi - chart.flatPhysicalWidth
  le_width : beta ≤ chart.flatPhysicalWidth
  clean_bottom : ∀ t : NNReal, 0 < (t:ℝ) →
    ν (map (retainedApexBottomSource positive.le le_pi t)) = 0 ∧
    α (map (retainedApexBottomSource positive.le le_pi t)) = 0
  clean_open : ∀ x : closedEuclideanSector beta, 0 < ‖x.1‖ →
    0 < Complex.arg x.1 → Complex.arg x.1 < beta →
      map x ∈ interior P ∧ ν (map x) = 0 ∧ α (map x) = 0
  first_top : beta < min Real.pi (α (map (flatLinkSectorApex positive.le))) →
    ∃ t : NNReal, 0 < (t:ℝ) ∧
      map (retainedApexUpperSource positive.le le_pi t) ∈ pointSignedMarked ν α

/-- No supplied sector: the original current state and one actual clean ray
produce the actual positive sector and its first-contact alternative. -/
theorem PointGeometricCutState.construct_sector
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (R : K.CleanRay) : Nonempty (PointConstructedCutSector a y P ν α) := by
  classical
  obtain ⟨C, hC, _⟩ := K.boundary_coeff (R.ray 0) (R.frontier 0)
  obtain ⟨D, hν, hα, hray, _, F, hd, _, hb, hopen, _, _, _, htop⟩ :=
    exists_point_actual_first_marked_sector ha y K.ambient K.region_eq
      K.toPointRetainedSignedHalfplaneState.isClosed K.connected.isPreconnected
      K.charts K.pieces K.boundary_cover K.budget
      K.toPointRetainedSignedHalfplaneState.marked_support K.boundary_formula K.interior_marked
      R.ray R.metric
      (fun t ↦ K.toPointRetainedSignedHalfplaneState.isClosed.frontier_subset (R.frontier t))
      R.frontier R.clean R.budget_supported C hC
  let σ : closedEuclideanSector D.beta → ℂ := fun x ↦ (F x).1
  have hbs (t : NNReal) : σ (retainedApexBottomSource D.beta_pos.le D.beta_pi t) = R.ray t := by
    have hv : (retainedApexBottomSource D.beta_pos.le D.beta_pi t).1 = (t : ℂ) := by
      simp [retainedApexBottomSource, sectorPolar, conePhase]
    let ht : (t : ℂ) ∈ closedEuclideanSector D.beta := hv ▸
      (retainedApexBottomSource D.beta_pos.le D.beta_pi t).2
    have he : retainedApexBottomSource D.beta_pos.le D.beta_pi t = ⟨(t : ℂ), ht⟩ :=
      Subtype.ext hv
    rw [he]
    exact hb t ht
  have hp : σ (flatLinkSectorApex D.beta_pos.le) = R.ray 0 := by
    have he : retainedApexBottomSource D.beta_pos.le D.beta_pi 0 = flatLinkSectorApex D.beta_pos.le :=
      Subtype.ext (sectorPolar_zero 0)
    rw [← he]
    exact hbs 0
  have hβα : D.beta ≤ α (σ (flatLinkSectorApex D.beta_pos.le)) := by
    rw [hp]
    simpa only [hα, hray] using D.beta_budget
  obtain ⟨E, hE, he⟩ := K.boundary_coeff _ (hp.symm ▸ R.frontier 0)
  have hwidth : D.beta ≤ E.flatPhysicalWidth :=
    (le_min D.beta_pi hβα).trans (K.budget.min_pi_budget_le_boundary_angle _ he)
  refine ⟨{
    beta := D.beta
    positive := D.beta_pos
    le_pi := D.beta_pi
    map := σ
    metric := hd
    mem_region := fun x ↦ (F x).2
    bottom_frontier := fun t ↦ (hbs t).symm ▸ R.frontier t
    le_budget := hβα
    apex_supported := hp.symm ▸ R.budget_supported
    chart := E
    admissible := hE
    chart_coeff := he
    le_width := hwidth
    clean_bottom := ?_
    clean_open := ?_
    first_top := ?_ }⟩
  · intro t ht
    rw [hbs t]
    exact pointSigned_eq_zero_off_marked
      (pointMetricRay_positive_not_marked y R.ray R.metric R.clean t ht)
  · intro x hx0 hxarg hxβ
    obtain ⟨hi, hm⟩ := hopen x (retainedSector_strict_source_interior D.beta_pi x hx0 hxarg hxβ)
    exact ⟨hi, pointSigned_eq_zero_off_marked hm⟩
  · intro hc
    rw [hp] at hc
    obtain ⟨x, hm, _, L, hL, q, hq, hx, _⟩ := htop hc
    let t : NNReal := ⟨L, hL.le⟩
    have hq' : retainedApexUpperSource D.beta_pos.le D.beta_pi t = q := Subtype.ext hq.symm
    refine ⟨t, hL, ?_⟩
    rw [hq']
    change (F q).1 ∈ pointSignedMarked ν α
    rw [hx]
    exact hm

end RepulsiveCoulomb
