module

public import LeanResearch.RepulsiveCoulomb.PointFullSideRetainedChart
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk
public import LeanResearch.RepulsiveCoulomb.PointRetainedWidthInvariance
public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart
public import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfplaneHomeomorphisms

@[expose] public section

/-! Whole metric disks are restricted literally. The two retained side charts
are constructed in one normalized actual cone chart with complementary FULL
ordered intervals, including reflex intervals and coalesced positive atoms. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def PointFlatLinkConeDisk.restrict {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {r : ℝ} (hr : 0 < r) (hrC : r ≤ C.radius) :
    PointFlatLinkConeDisk a y p where
  chart := C.chart
  radius := r
  radius_pos := hr
  center := C.center
  source := fun _ hz ↦ C.source (hz.trans hrC)
  onto := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      change ‖C.chart z‖ ≤ r
      rw [C.norm_chart (hz.trans hrC)]
      exact hz
    · intro z hz w hw he
      exact C.onto.injOn (hz.trans hrC) (hw.trans hrC) he
    · intro w hw
      obtain ⟨z, hz, he⟩ := C.onto.surjOn (hw.trans hrC)
      refine ⟨z, ?_, he⟩
      change (pointSmoothConformalEDist a y z p).toReal ≤ r
      rw [← C.norm_chart hz, he]
      exact hw
  metric := fun z hz w hw ↦ C.metric z (hz.trans hrC) w (hw.trans hrC)

theorem pointClosedRadialInterval_radius_iff {r R lo hi : ℝ} (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    z ∈ pointClosedRadialInterval R lo hi ↔ z ∈ pointClosedRadialInterval r lo hi := by
  constructor
  · rintro ⟨s, hs, θ, hθ, he⟩
    refine ⟨s, ⟨hs.1, ?_⟩, θ, hθ, he⟩
    rw [he, pointRadialSectorPoint_norm hs.1] at hz
    exact hz
  · rintro ⟨s, hs, θ, hθ, he⟩
    exact ⟨s, ⟨hs.1, hs.2.trans hrR⟩, θ, hθ, he⟩

@[simp] theorem pointRadialSectorPoint_two_pi (r : ℝ) :
    pointRadialSectorPoint r (2 * Real.pi) = pointRadialSectorPoint r 0 := by
  unfold pointRadialSectorPoint
  rw [show 2 * Real.pi = 0 + 2 * Real.pi by ring, Circle.exp_add_two_pi]

theorem lineClosedTerminalSector_iff_closed_interval
    {z : ℂ} {R θ : ℝ} (hz : z ∈ ball (0 : ℂ) R) (hθ : θ < 2 * Real.pi) :
    z ∈ lineClosedTerminalSector R θ ↔ z ∈ pointClosedRadialInterval R θ (2 * Real.pi) := by
  constructor
  · rintro ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩)
    · exact ⟨r, ⟨hr.1, hr.2.le⟩, 2 * Real.pi, ⟨hθ.le, le_rfl⟩,
        (pointRadialSectorPoint_two_pi r).symm⟩
    · exact ⟨r, ⟨hr.1, hr.2.le⟩, θ, ⟨le_rfl, hθ.le⟩, rfl⟩
    · exact ⟨r, ⟨hr.1.le, hr.2.le⟩, φ, ⟨hφ.1.le, hφ.2.le⟩, rfl⟩
  · rintro ⟨r, hr, φ, hφ, rfl⟩
    have hrR : r < R := by
      simpa only [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.1] using hz
    by_cases hφ0 : φ = 2 * Real.pi
    · exact Or.inl (Or.inl ⟨r, ⟨hr.1, hrR⟩, by simp only [hφ0, pointRadialSectorPoint_two_pi]⟩)
    by_cases hφθ : φ = θ
    · exact Or.inl (Or.inr ⟨r, ⟨hr.1, hrR⟩, by rw [hφθ]⟩)
    by_cases hr0 : r = 0
    · exact Or.inl (Or.inl ⟨0, ⟨le_rfl, by linarith⟩, by simp only [hr0, pointRadialSectorPoint_zero]⟩)
    · exact Or.inr ⟨(r, φ), ⟨⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hrR⟩,
        ⟨lt_of_le_of_ne hφ.1 (Ne.symm hφθ), lt_of_le_of_ne hφ.2 hφ0⟩⟩, rfl⟩

/-- The membership test is in the same genuine whole cone disk. Its radius is
shrunk before creating the retained chart, so the open-radius side formulas
cover the ENTIRE closed metric disk required by the retained-neighborhood API. -/
def PointFlatLinkConeDisk.retainedOfInterval {m : ℕ} {a : Fin m → ℝ}
    {y : Fin m → ℂ} {p : ℂ} (C : PointFlatLinkConeDisk a y p)
    {P : Set ℂ} {lo hi : ℝ} (hwidth : lo < hi) (hfull : hi-lo ≤ 2*Real.pi)
    (hside : ∀ z ∈ ball (0 : ℂ) C.radius,
      C.chart.symm z ∈ P ↔ z ∈ pointClosedRadialInterval C.radius lo hi) :
    PointRetainedConeNeighborhood a y P p := by
  let r := C.radius / 2
  have hr : 0 < r := half_pos C.radius_pos
  have hrC : r ≤ C.radius := by dsimp [r]; linarith [C.radius_pos]
  let E := C.restrict hr hrC
  exact
    { chart := E.chart
      radius := E.radius
      radius_pos := E.radius_pos
      center := E.center
      source := E.source
      onto := E.onto
      metric := E.metric
      lo := lo
      hi := hi
      width_pos := hwidth
      width_le_full := hfull
      retained := by
        intro z hz
        have hzC := hz.trans hrC
        have hn : ‖C.chart z‖ ≤ r := (C.norm_chart hzC).trans_le hz
        have hball : C.chart z ∈ ball (0 : ℂ) C.radius := by
          rw [mem_ball, dist_zero_right]
          exact hn.trans_lt (by dsimp [r]; linarith [C.radius_pos])
        have hs := hside (C.chart z) hball
        rw [C.chart.left_inv (C.source hzC)] at hs
        exact hs.trans (pointClosedRadialInterval_radius_iff hrC hn) }

/-- A complete metric line determines genuine retained charts at EVERY line
point for both fixed global sides. Their widths add to the full ambient cone
angle. This does not prescribe which side is the removed strip. -/
theorem pointMetricLine_construct_complementary_retained_charts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (line : ℝ → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (line u) (line v)).toReal = dist u v)
    (D : PlanarLineHalfplaneHomeomorphs line) (s : ℝ) :
    ∃ C : PointRetainedConeNeighborhood a y (closure D.positive) (line s),
      ∃ E : PointRetainedConeNeighborhood a y (closure D.negative) (line s),
        C.chart = E.chart ∧
        ((C.lo = 0 ∧ C.hi = E.lo ∧ E.hi = 2*Real.pi) ∨
          (E.lo = 0 ∧ E.hi = C.lo ∧ C.hi = 2*Real.pi)) ∧
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
    refine ⟨C,E,rfl,Or.inl ⟨rfl,rfl,rfl⟩,?_⟩
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
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
    refine ⟨C,E,rfl,Or.inr ⟨rfl,rfl,rfl⟩,?_⟩
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    change (coalescedPointExponent a y (line s)/2+1)*(2*Real.pi-θ) +
      (coalescedPointExponent a y (line s)/2+1)*(θ-0) = _
    ring

end RepulsiveCoulomb
