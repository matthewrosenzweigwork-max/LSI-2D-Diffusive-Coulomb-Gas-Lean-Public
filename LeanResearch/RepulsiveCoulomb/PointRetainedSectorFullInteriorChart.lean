module

public import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk
public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. Genuine full retained cone charts at ordinary
interior points, including ambient cone atoms. This does not infer flatness. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem retainedSector_full_radial_disk (R : ℝ) :
    pointClosedRadialInterval R 0 (2*Real.pi) = {z : ℂ | ‖z‖ ≤ R} := by
  ext z
  constructor
  · rintro ⟨r,hr,θ,hθ,he⟩
    change ‖z‖ ≤ R
    rw [he,pointRadialSectorPoint_norm hr.1]
    exact hr.2
  · intro hz
    change ‖z‖ ≤ R at hz
    by_cases hz0 : z = 0
    · refine ⟨0,⟨le_rfl,?_⟩,0,⟨le_rfl,by positivity⟩,?_⟩
      · simpa only [hz0,norm_zero] using hz
      · simp only [hz0,pointRadialSectorPoint_zero]
    · obtain ⟨θ,hθ,he⟩ := exists_pointRadialSectorPoint_angle z hz0
      exact ⟨‖z‖,⟨norm_nonneg z,hz⟩,θ,⟨hθ.1,hθ.2.le⟩,he.symm⟩

theorem pointRetainedSector_construct_full_interior_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (hp : p ∈ interior P) :
    ∃ C : PointRetainedConeNeighborhood a y P p, C.Full := by
  have hn : P ∈ @nhds ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact mem_interior_iff_mem_nhds.mp hp
  obtain ⟨ε,hε,hball⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hn
  obtain ⟨K⟩ := exists_pointFlatLinkConeDisk ha y p
  let r := min K.radius ε/2
  have hr : 0 < r := half_pos (lt_min K.radius_pos hε)
  have hrK : r ≤ K.radius := by dsimp [r]; linarith [min_le_left K.radius ε,lt_min K.radius_pos hε]
  have hrε : r < ε := by dsimp [r]; linarith [min_le_right K.radius ε,lt_min K.radius_pos hε]
  have hfull (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ r) : z ∈ P :=
    hball (hz.trans_lt hrε)
  let C : PointRetainedConeNeighborhood a y P p :=
    { chart := K.chart
      radius := r
      radius_pos := hr
      center := K.center
      source := fun z hz ↦ K.source (hz.trans hrK)
      onto := by
        refine ⟨?_,?_,?_⟩
        · intro z hz
          change ‖K.chart z‖ ≤ r
          rw [K.norm_chart (hz.trans hrK)]
          exact hz
        · intro z hz w hw he
          exact K.onto.injOn (hz.trans hrK) (hw.trans hrK) he
        · intro w hw
          obtain ⟨z,hz,he⟩ := K.onto.surjOn (hw.trans hrK)
          refine ⟨z,?_,he⟩
          change (pointSmoothConformalEDist a y z p).toReal ≤ r
          rw [← K.norm_chart hz,he]
          exact hw
      metric := fun z hz w hw ↦ K.metric z (hz.trans hrK) w (hw.trans hrK)
      lo := 0
      hi := 2*Real.pi
      width_pos := by positivity
      width_le_full := by simp
      retained := by
        intro z hz
        rw [retainedSector_full_radial_disk]
        exact iff_of_true (hfull z hz) ((K.norm_chart (hz.trans hrK)).trans_le hz) }
  exact ⟨C,hfull⟩

end RepulsiveCoulomb
