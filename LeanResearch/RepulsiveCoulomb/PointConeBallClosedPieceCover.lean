import LeanResearch.RepulsiveCoulomb.PointUnchangedConeSectorChart
import LeanResearch.RepulsiveCoulomb.OrderedEuclideanWedgeCover

/-! SOURCE-ONLY, UNCOMPILED. The finite closed angular cover lives on an
actual open old cone ball in the original plane. Its openness and whole-ball
coverage are derived from the genuine ambient cone chart, independently of
the yet-to-be-pasted new branches. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def pointConeOpenBall
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (R : ℝ) : Set ℂ :=
  C.chart.source ∩ C.chart ⁻¹' ball 0 R

theorem pointConeOpenBall_isOpen
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (R : ℝ) : IsOpen (pointConeOpenBall C R) :=
  C.chart.continuousOn.isOpen_inter_preimage C.chart.open_source isOpen_ball

theorem mem_pointConeOpenBall_iff
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {R : ℝ} (hRC : R ≤ C.radius) (z : ℂ) :
    z ∈ pointConeOpenBall C R ↔ (pointSmoothConformalEDist a y z p).toReal < R := by
  constructor
  · rintro ⟨hzS, hzn⟩
    have hnorm : ‖C.chart z‖ < R := by
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hzn
    obtain ⟨w, hw, hcw⟩ := C.onto.surjOn (hnorm.le.trans hRC)
    have hwz : w = z := C.chart.injOn (C.source hw) hzS hcw
    subst w
    rw [← C.norm_chart hw]
    exact hnorm
  · intro hz
    have hzC : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius := hz.le.trans hRC
    refine ⟨C.source hzC, ?_⟩
    change dist (C.chart z) 0 < R
    rw [dist_zero_right, C.norm_chart hzC]
    exact hz

theorem pointConeOpenBall_center
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {R : ℝ} (hR : 0 < R) : p ∈ pointConeOpenBall C R := by
  refine ⟨C.center_mem, ?_⟩
  change dist (C.chart p) 0 < R
  simpa only [C.center, dist_self] using hR

/-- Literal closed angular pieces in the original open source neighborhood. -/
def pointConeBallAngularPiece
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (R lo hi : ℝ) : Set (pointConeOpenBall C R) :=
  {z | C.chart z.1 ∈ flatLinkOccupiedDisk R lo hi}

theorem pointConeBallAngularPiece_isClosed
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (R lo hi : ℝ) :
    IsClosed (pointConeBallAngularPiece C R lo hi) := by
  have hcont : Continuous (fun z : pointConeOpenBall C R ↦ C.chart z.1) :=
    (C.chart.continuousOn.mono inter_subset_left).restrict
  exact (flatLinkOccupiedDisk_isClosed R lo hi).preimage hcont

/-- The source cover is the whole original open cone ball. It is proved by
polar representation and the constructed ordered consecutive interval cover. -/
theorem pointConeBallAngularPieces_cover
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {N : ℕ} (hN : 0 < N)
    (width : ℕ → ℝ) (htotal : linkCumulativeWidth width N = 2 * Real.pi)
    (R : ℝ) : ∀ z : pointConeOpenBall C R, ∃ i : Fin N,
      z ∈ pointConeBallAngularPiece C R (linkCumulativeWidth width i.1)
        (linkCumulativeWidth width (i.1 + 1)) := by
  intro z
  have hz : ‖C.chart z.1‖ ≤ R := by
    have hh := z.2.2
    change dist (C.chart z.1) 0 < R at hh
    rw [dist_zero_right] at hh
    exact hh.le
  exact orderedEuclideanWedges_cover hN width htotal R hz

end RepulsiveCoulomb
