module

public import LeanResearch.RepulsiveCoulomb.PointRetainedIntervalLocalMetric
public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Transfer every field of a genuine WHOLE
retained interval chart to a locally identical region. This handles unchanged
old boundary points of the translated cut, not its unresolved new corner.
The constructor shrinks the ambient disk; it never truncates a reflex angle. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

private theorem translatedGerm_interval_radius_iff {r R lo hi : ℝ} (hrR : r ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    z ∈ pointClosedRadialInterval R lo hi ↔ z ∈ pointClosedRadialInterval r lo hi := by
  constructor
  · rintro ⟨s,hs,θ,hθ,he⟩
    refine ⟨s,⟨hs.1,?_⟩,θ,hθ,he⟩
    rw [he,pointRadialSectorPoint_norm hs.1] at hz
    exact hz
  · rintro ⟨s,hs,θ,hθ,he⟩
    exact ⟨s,⟨hs.1,hs.2.trans hrR⟩,θ,hθ,he⟩

/-- Literal same-germ transport constructs a full retained cone neighborhood.
The input is the actual old chart, not a new residual chart or angle witness. -/
def PointRetainedConeNeighborhood.translatedGerm
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → (z ∈ P ↔ z ∈ Q)) :
    PointRetainedConeNeighborhood a y Q p := by
  let r := min C.radius ε
  have hr : 0 < r := lt_min C.radius_pos hε
  have hrC : r ≤ C.radius := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  have hnorm (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
      ‖C.chart z‖ = (pointSmoothConformalEDist a y z p).toReal := by
    have hp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
      rw [pointSmoothConformalEDist_self,ENNReal.toReal_zero]
      exact C.radius_pos.le
    rw [C.metric z hz p hp,C.center,pointClassicalConeDist_apex]
  exact
    { chart := C.chart
      radius := r
      radius_pos := hr
      center := C.center
      source := fun z hz ↦ C.source (hz.trans hrC)
      onto := by
        refine ⟨?_,?_,?_⟩
        · intro z hz
          change ‖C.chart z‖ ≤ r
          rw [hnorm z (hz.trans hrC)]
          exact hz
        · intro z hz w hw he
          exact C.onto.injOn (hz.trans hrC) (hw.trans hrC) he
        · intro w hw
          obtain ⟨z,hz,he⟩ := C.onto.surjOn (hw.trans hrC)
          refine ⟨z,?_,he⟩
          change (pointSmoothConformalEDist a y z p).toReal ≤ r
          rw [← hnorm z hz,he]
          exact hw
      metric := fun z hz w hw ↦ C.metric z (hz.trans hrC) w (hw.trans hrC)
      lo := C.lo
      hi := C.hi
      width_pos := C.width_pos
      width_le_full := C.width_le_full
      retained := by
        intro z hz
        have hn : ‖C.chart z‖ ≤ r := (hnorm z (hz.trans hrC)).trans_le hz
        exact (heq z (hz.trans hrε)).symm.trans
          ((C.retained z (hz.trans hrC)).trans (translatedGerm_interval_radius_iff hrC hn)) }

@[simp] theorem PointRetainedConeNeighborhood.translatedGerm_width
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → (z ∈ P ↔ z ∈ Q)) :
    (C.translatedGerm hε heq).flatPhysicalWidth = C.flatPhysicalWidth := rfl

/-- Away from the closed removed image, the literal residual has precisely
the old region's germ, and the previous constructor supplies every chart field. -/
theorem pointTranslatedStrip_retained_chart_away_from_image
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P S : Set ℂ} (hP : IsClosed P) (hS : IsClosed S) {p : ℂ} (hpS : p ∉ S)
    (C : PointRetainedConeNeighborhood a y P p) :
    ∃ E : PointRetainedConeNeighborhood a y (closure (P \ S)) p,
      E.chart = C.chart ∧ E.lo = C.lo ∧ E.hi = C.hi ∧
      E.flatPhysicalWidth = C.flatPhysicalWidth := by
  have hSm : @IsClosed ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace S := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hnhds : Sᶜ ∈ @nhds ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact hS.isOpen_compl.mem_nhds hpS
  obtain ⟨ε,hε,hball⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hnhds
  have hhalf : 0 < ε / 2 := half_pos hε
  have heq : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε/2 →
      (z ∈ P ↔ z ∈ closure (P \ S)) := by
    intro z hz
    have hzS : z ∉ S := hball (by
      change (pointSmoothConformalEDist a y z p).toReal < ε
      exact hz.trans_lt (half_lt_self hε))
    constructor
    · intro hzP
      exact subset_closure ⟨hzP,hzS⟩
    · intro hzP
      exact (closure_minimal (sdiff_subset : P \ S ⊆ P) hP) hzP
  exact ⟨C.translatedGerm hhalf heq,rfl,rfl,rfl,rfl⟩

end RepulsiveCoulomb
