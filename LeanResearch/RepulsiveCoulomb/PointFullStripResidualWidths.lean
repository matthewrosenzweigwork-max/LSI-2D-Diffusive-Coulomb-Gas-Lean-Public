import LeanResearch.RepulsiveCoulomb.PointFullStripTopOccupancy
import LeanResearch.RepulsiveCoulomb.PointFullStripResidualHalfplane

/-! Identify the halfdisk with the correct global removed side, compare its
actual retained width, and subtract from the complementary whole cone interval.
The coefficient identity is proved for every top point, not just atoms of a
chosen finite list. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem pointInterior_exists_closed_metric_ball
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (hp : p ∈ interior P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z,
      (pointSmoothConformalEDist a y z p).toReal ≤ ε → z ∈ P := by
  have hn : P ∈ @nhds ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact mem_interior_iff_mem_nhds.mp hp
  obtain ⟨r, hr, hball⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hn
  refine ⟨r/2, half_pos hr, fun z hz ↦ hball ?_⟩
  change (pointSmoothConformalEDist a y z p).toReal < r
  linarith

/-- The full-strip side assignment determines an ACTUAL local equality of
closed sets. In particular a top atom is an OLD interior point and the old
exterior cannot contribute to its sufficiently small cone disk. -/
theorem pointFullStrip_removed_side_local_germ
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P S : Set ℂ} {top : ℝ → ℂ} (D : PlanarLineHalfplaneHomeomorphs top)
    (hremoved : Pᶜ ∪ (S \ range top) = D.positive)
    (htopS : range top ⊆ S) {p : ℂ} (hp : p ∈ interior P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z,
      (pointSmoothConformalEDist a y z p).toReal ≤ ε →
        (z ∈ closure D.positive ↔ z ∈ S) := by
  obtain ⟨ε,hε,hball⟩ := pointInterior_exists_closed_metric_ball ha y hp
  refine ⟨ε,hε,?_⟩
  intro z hz
  have hzP := hball z hz
  rw [closure_eq_self_union_frontier, D.positive_frontier, ← hremoved]
  constructor
  · rintro ((hz | hz) | hz)
    · exact False.elim (hz hzP)
    · exact hz.1
    · exact htopS hz
  · intro hzS
    by_cases hzt : z ∈ range top
    · exact Or.inr hzt
    · exact Or.inl (Or.inr ⟨hzS,hzt⟩)

/-- Both actual closed sides have genuine charts with full intervals. The
removed side has physical width pi because it has the same local germ as the
actual isometric halfdisk; its complement therefore has width lambda_X-pi. -/
theorem pointFullStrip_construct_residual_top_widths
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (hpositive : ∀ z, 0 < z.1.im → (F z).1 ∈ interior P)
    (D : PlanarLineHalfplaneHomeomorphs (fun r ↦ (F (fullStripTop hh.le r)).1))
    (hremoved : Pᶜ ∪ (range (fun z ↦ (F z).1) \
      range (fun r ↦ (F (fullStripTop hh.le r)).1)) = D.positive)
    (s : ℝ) :
    ∃ C : PointRetainedConeNeighborhood a y (closure D.positive) (F (fullStripTop hh.le s)).1,
      ∃ E : PointRetainedConeNeighborhood a y (closure D.negative) (F (fullStripTop hh.le s)).1,
        C.chart = E.chart ∧
        ((C.lo = 0 ∧ C.hi = E.lo ∧ E.hi = 2*Real.pi) ∨
          (E.lo = 0 ∧ E.hi = C.lo ∧ C.hi = 2*Real.pi)) ∧
        C.flatPhysicalWidth = Real.pi ∧
        E.flatPhysicalWidth = (1+coalescedPointExponent a y (F (fullStripTop hh.le s)).1/2)*
          (2*Real.pi) - Real.pi ∧
        Real.pi - E.flatPhysicalWidth = -Real.pi * coalescedPointExponent a y (F (fullStripTop hh.le s)).1 ∧
        E.Admissible := by
  have ht : ∀ u v, (pointSmoothConformalEDist a y
      (F (fullStripTop hh.le u)).1 (F (fullStripTop hh.le v)).1).toReal = dist u v := by
    intro u v
    rw [hF]
    exact (fullStripTop_isometry hh.le).dist_eq u v
  obtain ⟨C,E,hchart,hinterval,hsum⟩ :=
    pointMetricLine_construct_complementary_retained_charts ha y _ ht D s
  obtain ⟨K,_,_,hKwidth⟩ := pointFullStrip_construct_top_strip_retained_chart ha y hh F hF s
  have htS : range (fun r ↦ (F (fullStripTop hh.le r)).1) ⊆ range (fun z ↦ (F z).1) := by
    rintro z ⟨r,rfl⟩; exact mem_range_self _
  obtain ⟨ε,hε,heq⟩ := pointFullStrip_removed_side_local_germ ha y D hremoved htS
    (hpositive (fullStripTop hh.le s) hh)
  have hw : C.flatPhysicalWidth = K.flatPhysicalWidth := by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y (F (fullStripTop hh.le s)).1/2) 1] using
      C.physical_width_eq_of_local_eq K hε heq
  have hC : C.flatPhysicalWidth = Real.pi := hw.trans hKwidth
  have hE : E.flatPhysicalWidth =
      (1+coalescedPointExponent a y (F (fullStripTop hh.le s)).1/2)*(2*Real.pi)-Real.pi := by
    rw [hC] at hsum
    linarith
  refine ⟨C,E,hchart,hinterval,hC,hE,?_,?_⟩
  · rw [hE]
    ring
  · unfold PointRetainedConeNeighborhood.Admissible
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth at hE
    nlinarith

/-- Every genuine retained chart of the actual new side has the same physical
width, regardless of chart normalization or orientation. -/
theorem pointFullStrip_residual_top_width_unique
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {Q : Set ℂ} {p : ℂ}
    (E C : PointRetainedConeNeighborhood a y Q p)
    (hE : E.flatPhysicalWidth = (1+coalescedPointExponent a y p/2)*(2*Real.pi)-Real.pi) :
    C.flatPhysicalWidth = (1+coalescedPointExponent a y p/2)*(2*Real.pi)-Real.pi := by
  have hw : C.flatPhysicalWidth = E.flatPhysicalWidth := by
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y p/2) 1] using C.physical_width_eq E
  exact hw.trans hE

/-- A full unwrapped circle is represented as a set, never claimed to be an
injective angle interval. The endpoints 0 and 2*pi are correctly identified. -/
theorem pointClosedRadialInterval_full_disk (r : ℝ) :
    pointClosedRadialInterval r 0 (2*Real.pi) = {z : ℂ | ‖z‖ ≤ r} := by
  ext z
  constructor
  · rintro ⟨s,hs,θ,hθ,he⟩
    change ‖z‖ ≤ r
    rw [he,pointRadialSectorPoint_norm hs.1]
    exact hs.2
  · intro hz
    by_cases hz0 : z = 0
    · refine ⟨0,⟨le_rfl,?_⟩,0,⟨le_rfl,by positivity⟩,?_⟩
      · simpa only [Set.mem_setOf_eq,hz0,norm_zero] using hz
      · simp only [hz0,pointRadialSectorPoint_zero]
    · obtain ⟨θ,hθ,he⟩ := exists_pointRadialSectorPoint_angle z hz0
      exact ⟨‖z‖,⟨norm_nonneg z,hz⟩,θ,⟨hθ.1,hθ.2.le⟩,he.symm⟩

/-- Genuine ambient cone charts give actual FULL retained-circle charts at
arbitrary interior points, including interior positive atoms. -/
theorem pointInterior_construct_full_retained_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (hp : p ∈ interior P) :
    ∃ C : PointRetainedConeNeighborhood a y P p,
      C.lo = 0 ∧ C.hi = 2*Real.pi ∧
      C.flatPhysicalWidth = (1+coalescedPointExponent a y p/2)*(2*Real.pi) := by
  obtain ⟨ε,hε,hball⟩ := pointInterior_exists_closed_metric_ball ha y hp
  obtain ⟨K⟩ := exists_pointFlatLinkConeDisk ha y p
  let r := min ε K.radius
  have hr : 0 < r := lt_min hε K.radius_pos
  let E := K.restrict hr (min_le_right _ _)
  let C : PointRetainedConeNeighborhood a y P p :=
    { chart := E.chart
      radius := E.radius
      radius_pos := E.radius_pos
      center := E.center
      source := E.source
      onto := E.onto
      metric := E.metric
      lo := 0
      hi := 2*Real.pi
      width_pos := by positivity
      width_le_full := by simp
      retained := by
        intro z hz
        have hzP := hball z (hz.trans (min_le_left ε K.radius))
        have hn : ‖E.chart z‖ ≤ r := (E.norm_chart hz).trans_le hz
        rw [pointClosedRadialInterval_full_disk]
        exact iff_of_true hzP hn }
  refine ⟨C,rfl,rfl,?_⟩
  unfold PointRetainedConeNeighborhood.flatPhysicalWidth
  change (coalescedPointExponent a y p/2+1)*(2*Real.pi-0) =
    (1+coalescedPointExponent a y p/2)*(2*Real.pi)
  ring

end RepulsiveCoulomb
