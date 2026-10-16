module

public import LeanResearch.RepulsiveCoulomb.PointRetainedRegionIntrinsicMetric
public import LeanResearch.RepulsiveCoulomb.MetricRegionPathLocalization
public import LeanResearch.RepulsiveCoulomb.MetricRegionPathTransport

@[expose] public section

/-! The exact local interval-cone length model of a literal retained region.
Its model distance is itself the genuine path infimum in the retained cone
interval. Exit cost identifies it with the global region distance on a smaller
disk. Complement-angle admissibility and ambient convexity are not used. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

def PointRetainedConeNeighborhood.closedBallRestriction {m : ℕ} {a : Fin m → ℝ}
    {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p) :
    PointRetainedConeNeighborhood a y
      (P ∩ {z | (pointSmoothConformalEDist a y z p).toReal ≤ C.radius}) p where
  chart := C.chart
  radius := C.radius
  radius_pos := C.radius_pos
  center := C.center
  source := C.source
  onto := C.onto
  metric := C.metric
  lo := C.lo
  hi := C.hi
  width_pos := C.width_pos
  width_le_full := C.width_le_full
  retained z hz := by
    change (z ∈ P ∧ (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) ↔ _
    rw [and_iff_left hz]
    exact C.retained z hz

def pointRetainedIntervalEDist {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p) (u v : ℂ) : ℝ≥0∞ :=
  @metricRegionPathEDist ℂ (pointClassicalConeMetricSpace a y p)
    (pointClosedRadialInterval C.radius C.lo C.hi) u v

theorem pointClosedRadialInterval_norm_le {R lo hi : ℝ} {w : ℂ}
    (hw : w ∈ pointClosedRadialInterval R lo hi) : ‖w‖ ≤ R := by
  obtain ⟨r, hr, θ, hθ, rfl⟩ := hw
  rw [pointRadialSectorPoint_norm hr.1]
  exact hr.2

/-- Transport all constrained curves in the actual cone patch, in both
directions, including curves through its apex. -/
theorem PointRetainedConeNeighborhood.patch_intrinsic_eq {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {p x z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hx : x ∈ P) (hz : z ∈ P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
    pointRegionIntrinsicEDist ha y
      (P ∩ {u | (pointSmoothConformalEDist a y u p).toReal ≤ C.radius}) x z =
      pointRetainedIntervalEDist C (C.chart x) (C.chart z) := by
  let Q := P ∩ {u | (pointSmoothConformalEDist a y u p).toReal ≤ C.radius}
  let S := pointClosedRadialInterval C.radius C.lo C.hi
  let dX := pointSmoothConformalMetricSpace ha y
  let dY := pointClassicalConeMetricSpace a y p
  have hfc : @ContinuousOn ℂ ℂ dX.toUniformSpace.toTopologicalSpace
      dY.toUniformSpace.toTopologicalSpace C.chart Q := by
    change @ContinuousOn ℂ ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (pointClassicalConeMetricSpace a y p).toUniformSpace.toTopologicalSpace C.chart Q
    rw [pointSmoothConformalMetricSpace_topology ha y, pointClassicalConeMetricSpace_topology a y p]
    exact C.chart.continuousOn.mono (fun u hu ↦ C.source hu.2)
  have hfmap : MapsTo C.chart Q S := fun u hu ↦ (C.retained u hu.2).mp hu.1
  have htarget : S ⊆ C.chart.target := by
    intro w hw
    obtain ⟨u, hu, huw⟩ := C.onto.surjOn (pointClosedRadialInterval_norm_le hw)
    exact huw ▸ C.chart.mapsTo (C.source hu)
  have hgmap : MapsTo C.chart.symm S Q := by
    intro w hw
    obtain ⟨u, hu, huw⟩ := C.onto.surjOn (pointClosedRadialInterval_norm_le hw)
    have hinv : C.chart.symm w = u := by rw [← huw, C.chart.left_inv (C.source hu)]
    rw [hinv]
    exact ⟨(C.retained u hu).mpr (huw.symm ▸ hw), hu⟩
  have hgc : @ContinuousOn ℂ ℂ dY.toUniformSpace.toTopologicalSpace
      dX.toUniformSpace.toTopologicalSpace C.chart.symm S := by
    change @ContinuousOn ℂ ℂ
      (pointClassicalConeMetricSpace a y p).toUniformSpace.toTopologicalSpace
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace C.chart.symm S
    rw [pointSmoothConformalMetricSpace_topology ha y, pointClassicalConeMetricSpace_topology a y p]
    exact C.chart.continuousOn_symm.mono htarget
  have hfm : ∀ u ∈ Q, ∀ v ∈ Q,
      @edist ℂ dY.toEDist (C.chart u) (C.chart v) = @edist ℂ dX.toEDist u v := by
    intro u hu v hv
    rw [@edist_dist ℂ dY.toPseudoMetricSpace, @edist_dist ℂ dX.toPseudoMetricSpace]
    exact congrArg ENNReal.ofReal (C.metric u hu.2 v hv.2).symm
  have hgm : ∀ u ∈ S, ∀ v ∈ S,
      @edist ℂ dX.toEDist (C.chart.symm u) (C.chart.symm v) = @edist ℂ dY.toEDist u v := by
    intro u hu v hv
    have h := hfm (C.chart.symm u) (hgmap hu) (C.chart.symm v) (hgmap hv)
    rw [C.chart.right_inv (htarget hu), C.chart.right_inv (htarget hv)] at h
    exact h.symm
  have heq := @metricRegionPathEDist_map_eq ℂ ℂ dX dY Q S C.chart C.chart.symm
    hfc hgc hfmap hgmap hfm hgm
    (fun u hu ↦ C.chart.left_inv (C.source hu.2)) x z ⟨hx, hxR⟩ ⟨hz, hzR⟩
  rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
  exact heq.symm

/-- Exact smaller-neighborhood model, proved by comparing real path lengths
with the cost of leaving the full chart disk. -/
theorem PointRetainedConeNeighborhood.intrinsic_local_model {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {p x z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hp : p ∈ P) (hx : x ∈ P) (hz : z ∈ P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius / 4)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius / 4) :
    pointRegionIntrinsicEDist ha y P x z = pointRetainedIntervalEDist C (C.chart x) (C.chart z) := by
  let dX := pointSmoothConformalMetricSpace ha y
  let Q := P ∩ {u | (pointSmoothConformalEDist a y u p).toReal ≤ C.radius}
  have hxfull : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius := by linarith [C.radius_pos]
  have hzfull : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius := by linarith [C.radius_pos]
  have hpQ : p ∈ Q := by
    refine ⟨hp, ?_⟩
    change (pointSmoothConformalEDist a y p p).toReal ≤ C.radius
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  obtain ⟨f, hfc, hf0, hf1, hfP, hflen⟩ :=
    C.closedBallRestriction.exists_radial_path ha y hpQ ⟨hx, hxfull⟩ hxfull
  obtain ⟨g, hgc, hg0, hg1, hgP, hglen⟩ :=
    C.closedBallRestriction.exists_radial_path ha y hpQ ⟨hz, hzfull⟩ hzfull
  have hfc' : @Continuous ℝ ℂ _ dX.toUniformSpace.toTopologicalSpace f := by
    change @Continuous ℝ ℂ _ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace f
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hgc' : @Continuous ℝ ℂ _ dX.toUniformSpace.toTopologicalSpace g := by
    change @Continuous ℝ ℂ _ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace g
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  let γ : @MetricRegionLengthPath ℂ dX.toUniformSpace.toTopologicalSpace Q p x :=
    @MetricRegionLengthPath.mk ℂ dX.toUniformSpace.toTopologicalSpace Q p x f hfc' hf0 hf1 hfP
  let δ : @MetricRegionLengthPath ℂ dX.toUniformSpace.toTopologicalSpace Q p z :=
    @MetricRegionLengthPath.mk ℂ dX.toUniformSpace.toTopologicalSpace Q p z g hgc' hg0 hg1 hgP
  let γrev := @MetricRegionLengthPath.reverse ℂ dX.toUniformSpace.toTopologicalSpace Q p x γ
  let η := @MetricRegionLengthPath.trans ℂ dX.toUniformSpace.toTopologicalSpace Q x p z γrev δ
  have hη := @MetricRegionLengthPath.length_trans_le ℂ dX.toPseudoMetricSpace Q x p z γrev δ
  have hrevlen : @MetricRegionLengthPath.length ℂ dX.toPseudoMetricSpace Q x p γrev =
      pointConformalMetricLength ha y f 0 1 :=
    @MetricRegionLengthPath.length_reverse ℂ dX.toPseudoMetricSpace Q p x γ
  have hδlen : @MetricRegionLengthPath.length ℂ dX.toPseudoMetricSpace Q p z δ =
      pointConformalMetricLength ha y g 0 1 := rfl
  rw [hrevlen, hδlen, hflen, hglen] at hη
  have hbudget : pointSmoothConformalEDist a y p x + pointSmoothConformalEDist a y p z ≤
      ENNReal.ofReal (C.radius - (pointSmoothConformalEDist a y x p).toReal) := by
    rw [← ENNReal.ofReal_toReal (pointSmoothConformalEDist_lt_top ha y p x).ne,
      ← ENNReal.ofReal_toReal (pointSmoothConformalEDist_lt_top ha y p z).ne,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    rw [pointSmoothConformalEDist_comm a y p x, pointSmoothConformalEDist_comm a y p z]
    linarith [C.radius_pos]
  have hloc := @metricRegionPathEDist_closedBall_localization ℂ dX P p x z C.radius η
    (hη.trans hbudget)
  rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y P]
  exact hloc.trans ((pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y Q x z).symm.trans
    (C.patch_intrinsic_eq ha y hx hz hxfull hzfull))

end RepulsiveCoulomb
