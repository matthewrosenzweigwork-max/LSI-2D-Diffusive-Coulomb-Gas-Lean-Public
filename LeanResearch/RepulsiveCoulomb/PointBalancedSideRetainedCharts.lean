module

public import LeanResearch.RepulsiveCoulomb.PointActualBalancedLineAllMasses
public import LeanResearch.RepulsiveCoulomb.PointFullStripRetainedIntervals
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Genuine retained metric disks on the fixed
balanced sides, including both full physical intervals at every line atom.
No retained chart or coefficient identity is assumed by the final frontend. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_retainedConeNeighborhood_of_physical_interval
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (E F : OpenPartialHomeomorph ℂ ℂ)
    {δ r lo hi : ℝ} (hr : 0 < r) (hrδ : r ≤ δ)
    (hwidth : lo < hi) (hfull : hi - lo ≤ 2 * Real.pi)
    (hside : ∀ z ∈ ball (0 : ℂ) r,
      E.symm z ∈ P ↔ z ∈ pointClosedRadialInterval δ lo hi)
    (hpF : p ∈ F.source) (hF0 : F p = 0) (hFsrc : F.source ⊆ E.source)
    (hF : ∀ z, F z = coneRadialEquiv (coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) (E z))
    (hmetric : ∀ u ∈ F.source, ∀ v ∈ F.source,
      (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (F u) (F v)) :
    ∃ C : PointRetainedConeNeighborhood a y P p,
      C.chart = F ∧ C.lo = lo ∧ C.hi = hi := by
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hpE := hFsrc hpF
  have hE0 : E p = 0 := by
    apply (coneRadialEquiv α hα).injective
    rw [← hF, hF0, coneRadialEquiv_zero]
  let O := F.source ∩ E ⁻¹' ball (0 : ℂ) r
  have hO : O ∈ 𝓝 p := by
    refine inter_mem (F.open_source.mem_nhds hpF) ?_
    apply (E.continuousAt hpE).preimage_mem_nhds
    rw [hE0]
    exact isOpen_ball.mem_nhds (mem_ball_self hr)
  have hOm : O ∈ @nhds ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  obtain ⟨ε, hε, hεsub⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hOm
  have h0target : (0 : ℂ) ∈ F.target := hF0 ▸ F.mapsTo hpF
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (F.open_target.mem_nhds h0target)
  let R := min ε η / 2
  have hR : 0 < R := half_pos (lt_min hε hη)
  have hRε : R < ε := by dsimp [R]; linarith [min_le_left ε η, lt_min hε hη]
  have hRη : R < η := by dsimp [R]; linarith [min_le_right ε η, lt_min hε hη]
  have hlocal (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ R) :
      z ∈ F.source ∧ E z ∈ ball (0 : ℂ) r := by
    apply hεsub
    change (pointSmoothConformalEDist a y z p).toReal < ε
    exact hz.trans_lt hRε
  have hnorm (z : ℂ) (hz : z ∈ F.source) :
      (pointSmoothConformalEDist a y z p).toReal = ‖F z‖ := by
    rw [hmetric z hz p hpF, hF0, pointClassicalConeDist_apex]
  have honto : BijOn F {z : ℂ | (pointSmoothConformalEDist a y z p).toReal ≤ R}
      {z : ℂ | ‖z‖ ≤ R} := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      change ‖F z‖ ≤ R
      rwa [← hnorm z (hlocal z hz).1]
    · intro z hz w hw he
      exact F.injOn (hlocal z hz).1 (hlocal w hw).1 he
    · intro z hz
      have hzt : z ∈ F.target := hηsub (by
        rw [mem_ball, dist_zero_right]
        exact hz.trans_lt hRη)
      have hzs : F.symm z ∈ F.source := F.symm.mapsTo hzt
      refine ⟨F.symm z, ?_, F.right_inv hzt⟩
      change (pointSmoothConformalEDist a y (F.symm z) p).toReal ≤ R
      rw [hnorm _ hzs, F.right_inv hzt]
      exact hz
  let C : PointRetainedConeNeighborhood a y P p :=
    { chart := F
      radius := R
      radius_pos := hR
      center := hF0
      source := fun z hz => (hlocal z hz).1
      onto := honto
      metric := fun z hz w hw => hmetric z (hlocal z hz).1 w (hlocal w hw).1
      lo := lo
      hi := hi
      width_pos := hwidth
      width_le_full := hfull
      retained := by
        intro z hz
        obtain ⟨hzF, hzEball⟩ := hlocal z hz
        have hzE := hFsrc hzF
        have hmem : z ∈ P ↔ E z ∈ pointClosedRadialInterval δ lo hi := by
          simpa only [E.left_inv hzE] using hside (E z) hzEball
        have hbound : ‖F z‖ ≤ R := by rwa [← hnorm z hzF]
        have hEbound : ‖E z‖ ≤ δ := by
          exact (show ‖E z‖ < r by simpa only [mem_ball, dist_zero_right] using hzEball).le.trans hrδ
        have hrad : coneRadialEquiv α hα (E z) ∈ pointClosedRadialInterval R lo hi ↔
            E z ∈ pointClosedRadialInterval δ lo hi :=
          coneRadialEquiv_closed_interval_iff hα hEbound
            (show ‖coneRadialEquiv α hα (E z)‖ ≤ R by rwa [← hF])
        rw [← hF z] at hrad
        exact hmem.trans hrad.symm }
  exact ⟨C, rfl, rfl, rfl⟩


/-- The balanced theorem's raw/metric chart pair is converted into the two
literal retained charts. Complementary lower bounds are exactly admissibility. -/
theorem PointLinePhysicalSideWidths.retained_charts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {A B : Set ℂ} {p : ℂ} {wA wB : ℝ}
    (h : PointLinePhysicalSideWidths a y A B p wA wB)
    (hA : Real.pi ≤ wA) (hB : Real.pi ≤ wB) :
    ∃ C : PointRetainedConeNeighborhood a y (closure A) p,
      ∃ E : PointRetainedConeNeighborhood a y (closure B) p,
        C.flatPhysicalWidth = wA ∧ E.flatPhysicalWidth = wB ∧
        C.Admissible ∧ E.Admissible := by
  obtain ⟨F, G, δ, r, θ, hr, hrδ, hθ, hθ2, hwA, hwB, hside,
    hpG, hG0, hGsrc, hG, hmetric⟩ := h
  have hball (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) : z ∈ ball (0 : ℂ) δ :=
    ball_subset_ball hrδ hz
  obtain ⟨C, _, hlo, hhi⟩ := exists_retainedConeNeighborhood_of_physical_interval
    ha y F G hr hrδ hθ (by linarith : θ - 0 ≤ 2 * Real.pi)
    (fun z hz ↦ (hside z hz).1.trans
      (lineClosedInitialSector_iff_closed_interval (hball z hz) hθ))
    hpG hG0 hGsrc hG hmetric
  obtain ⟨E, _, hloE, hhiE⟩ := exists_retainedConeNeighborhood_of_physical_interval
    ha y F G hr hrδ hθ2 (by linarith : 2 * Real.pi - θ ≤ 2 * Real.pi)
    (fun z hz ↦ (hside z hz).2.trans
      (lineClosedTerminalSector_iff_closed_interval (hball z hz) hθ2))
    hpG hG0 hGsrc hG hmetric
  refine ⟨C, E, ?_, ?_, ?_, ?_⟩
  · unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    rw [hlo, hhi, sub_zero, hwA]
    ring
  · unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    rw [hloE, hhiE, hwB]
    ring
  · unfold PointRetainedConeNeighborhood.Admissible
    rw [hlo, hhi, sub_zero]
    simpa only [add_comm] using (hwB ▸ hB)
  · unfold PointRetainedConeNeighborhood.Admissible
    rw [hloE, hhiE]
    have he : 2 * Real.pi - (2 * Real.pi - θ) = θ := by ring
    rw [he]
    simpa only [add_comm] using (hwA ▸ hA)

theorem pointMetricLine_construct_admissible_retained_charts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (line : ℝ → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (line u) (line v)).toReal = dist u v)
    (D : PlanarLineHalfplaneHomeomorphs line) (s : ℝ) :
    ∃ C : PointRetainedConeNeighborhood a y (closure D.positive) (line s),
      ∃ E : PointRetainedConeNeighborhood a y (closure D.negative) (line s),
        Real.pi ≤ C.flatPhysicalWidth ∧ Real.pi ≤ E.flatPhysicalWidth ∧
        C.Admissible ∧ E.Admissible ∧
        C.flatPhysicalWidth + E.flatPhysicalWidth =
          (1 + coalescedPointExponent a y (line s)/2) * (2*Real.pi) := by
  let l : ℝ → ℂ := fun t ↦ line (s+t)
  have hl0 : l 0 = line s := by simp [l]
  have hlrange : range l = range line := pointMetricLine_recenter_range line s
  obtain ⟨F, R, θ, hR, hθ, hθ2, hpF, hF0, hsrc, honto, hmetric,
    htarget, hboundary, hleft, hright⟩ := exists_pointMetricLine_normalized_chart ha y l
      (pointMetricLine_recenter_metric y line hd s)
  rw [hl0] at hpF hF0 hsrc honto hmetric
  rw [hlrange] at hboundary
  let K : PointFlatLinkConeDisk a y (line s) := ⟨F,R,hR,hF0,hsrc,honto,hmetric⟩
  have hpU : line s ∈ closure D.positive := frontier_subset_closure (D.positive_frontier.symm ▸ mem_range_self s)
  have hpV : line s ∈ closure D.negative := frontier_subset_closure (D.negative_frontier.symm ▸ mem_range_self s)
  have hpart := pointDiskRay_complement_eq_sectors hR hθ hθ2
  have hpart' : ball (0 : ℂ) R \ (pointDiskRay R 0 ∪ pointDiskRay R θ) =
      pointOpenRadialSector R θ (2*Real.pi) ∪ pointOpenRadialSector R 0 θ := by
    simpa only [union_comm] using hpart
  have hside := pointRadialChart_region_side_choice D.positive_open D.negative_open D.disjoint
    D.cover hpU hpV F hpF hF0 hR hθ hθ2 htarget hboundary
  rcases hside with ⟨hSU,hTV⟩ | ⟨hSV,hTU⟩
  · have hU := chart_closed_side_membership D.disjoint D.cover D.positive_frontier F
      hboundary hpart hSU hTV
    have hV := chart_closed_side_membership D.disjoint.symm (by simpa only [union_comm] using D.cover)
      D.negative_frontier F hboundary hpart' hTV hSU
    let C := K.retainedOfInterval hθ (by linarith : θ-0 ≤ 2*Real.pi)
      (fun z hz ↦ (hU z hz).trans (lineClosedInitialSector_iff_closed_interval hz hθ))
    let E := K.retainedOfInterval hθ2 (by linarith : 2*Real.pi-θ ≤ 2*Real.pi)
      (fun z hz ↦ (hV z hz).trans (lineClosedTerminalSector_iff_closed_interval hz hθ2))
    refine ⟨C, E, ?_, ?_, ?_, ?_, ?_⟩
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(θ-0)
      simpa only [sub_zero, hl0] using hleft
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-θ)
      simpa only [hl0] using hright
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-(θ-0))
      simpa only [sub_zero, hl0] using hright
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-(2*Real.pi-θ))
      convert hleft using 1 <;> simp only [hl0] <;> ring
    · unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      change (coalescedPointExponent a y (line s)/2+1)*(θ-0) +
        (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-θ) = _
      ring
  · have hU := chart_closed_side_membership D.disjoint D.cover D.positive_frontier F
      hboundary hpart' hTU hSV
    have hV := chart_closed_side_membership D.disjoint.symm (by simpa only [union_comm] using D.cover)
      D.negative_frontier F hboundary hpart hSV hTU
    let C := K.retainedOfInterval hθ2 (by linarith : 2*Real.pi-θ ≤ 2*Real.pi)
      (fun z hz ↦ (hU z hz).trans (lineClosedTerminalSector_iff_closed_interval hz hθ2))
    let E := K.retainedOfInterval hθ (by linarith : θ-0 ≤ 2*Real.pi)
      (fun z hz ↦ (hV z hz).trans (lineClosedInitialSector_iff_closed_interval hz hθ))
    refine ⟨C, E, ?_, ?_, ?_, ?_, ?_⟩
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-θ)
      simpa only [hl0] using hright
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(θ-0)
      simpa only [sub_zero, hl0] using hleft
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-(2*Real.pi-θ))
      convert hleft using 1 <;> simp only [hl0] <;> ring
    · change Real.pi ≤ (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-(θ-0))
      simpa only [sub_zero, hl0] using hright
    · unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      change (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-θ) +
        (coalescedPointExponent a y (line s)/2+1)*(θ-0) = _
      ring


end RepulsiveCoulomb
