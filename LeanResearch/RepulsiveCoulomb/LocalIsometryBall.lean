import LeanResearch.RepulsiveCoulomb.ClassicalConeMetric

/-! A local distance-preserving chart identifies sufficiently small CLOSED metric
balls, including surjectivity onto the model ball. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem classicalConeMetricSpace_topology (α : ℝ) (hα : 0 ≤ α) :
    (classicalConeMetricSpace α hα).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := by
  change TopologicalSpace.induced (coneRadialEquiv α hα).symm
    (standardConeMetricSpace α hα).toUniformSpace.toTopologicalSpace = _
  rw [show (standardConeMetricSpace α hα).toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace ℂ) from pointSmoothConformalMetricSpace_topology _ _]
  exact (coneRadialHomeomorph α hα).symm.isInducing.eq_induced.symm

theorem exists_closedBall_isometry_of_local_chart {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source)
    (hd : ∀ u ∈ e.source, ∀ v ∈ e.source, dist (e u) (e v) = dist u v) :
    ∃ r : ℝ, 0 < r ∧ Nonempty ((closedBall x r) ≃ᵢ (closedBall (e x) r)) := by
  obtain ⟨rx, hrx, hxs⟩ := Metric.isOpen_iff.mp e.open_source x hx
  obtain ⟨ry, hry, hyt⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let r := min rx ry / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrx' : r < rx := by have := min_le_left rx ry; dsimp [r]; linarith
  have hry' : r < ry := by have := min_le_right rx ry; dsimp [r]; linarith
  have hs (u : closedBall x r) : (u : X) ∈ e.source :=
    hxs (lt_of_le_of_lt u.2 hrx')
  have ht (v : closedBall (e x) r) : (v : Y) ∈ e.target :=
    hyt (lt_of_le_of_lt v.2 hry')
  let f : closedBall x r → closedBall (e x) r := fun u ↦
    ⟨e u, by rw [mem_closedBall, hd u (hs u) x hx]; exact u.2⟩
  let g : closedBall (e x) r → closedBall x r := fun v ↦
    ⟨e.symm v, by
      rw [mem_closedBall, ← hd (e.symm v) (e.map_target (ht v)) x hx, e.right_inv (ht v)]
      exact v.2⟩
  refine ⟨r, hr, ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, isometry_toFun := ?_ }⟩⟩
  · intro u
    apply Subtype.ext
    exact e.left_inv (hs u)
  · intro v
    apply Subtype.ext
    exact e.right_inv (ht v)
  · apply isometry_iff_dist_eq.mpr
    intro u v
    exact hd u (hs u) v (hs v)

theorem exists_closedBall_bijOn_of_local_chart {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source)
    (hd : ∀ u ∈ e.source, ∀ v ∈ e.source, dist (e u) (e v) = dist u v) :
    ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ e.source ∧
      Set.BijOn e (closedBall x r) (closedBall (e x) r) := by
  obtain ⟨rx, hrx, hxs⟩ := Metric.isOpen_iff.mp e.open_source x hx
  obtain ⟨ry, hry, hyt⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let r := min rx ry / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrx' : r < rx := by have := min_le_left rx ry; dsimp [r]; linarith
  have hry' : r < ry := by have := min_le_right rx ry; dsimp [r]; linarith
  have hs : closedBall x r ⊆ e.source := fun u hu ↦ hxs (lt_of_le_of_lt hu hrx')
  have ht : closedBall (e x) r ⊆ e.target := fun v hv ↦ hyt (lt_of_le_of_lt hv hry')
  refine ⟨r, hr, hs, ?_, ?_, ?_⟩
  · intro u hu
    rw [mem_closedBall, hd u (hs hu) x hx]
    exact hu
  · exact e.injOn.mono hs
  · intro v hv
    refine ⟨e.symm v, ?_, e.right_inv (ht hv)⟩
    rw [mem_closedBall, ← hd (e.symm v) (e.map_target (ht hv)) x hx, e.right_inv (ht hv)]
    exact hv

def retopologizeOpenPartialHomeomorph {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (sX : TopologicalSpace X) (sY : TopologicalSpace Y)
    (hX : sX = tX) (hY : sY = tY) : @OpenPartialHomeomorph X Y sX sY := by
  subst sX
  subst sY
  exact e

theorem retopologizeOpenPartialHomeomorph_toPartialEquiv {X Y : Type*}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (sX : TopologicalSpace X) (sY : TopologicalSpace Y) (hX : sX = tX) (hY : sY = tY) :
    @PartialHomeomorph.toPartialEquiv X Y sX sY
      (@OpenPartialHomeomorph.toPartialHomeomorph X Y sX sY
        (@retopologizeOpenPartialHomeomorph X Y tX tY e sX sY hX hY)) =
      @PartialHomeomorph.toPartialEquiv X Y tX tY
        (@OpenPartialHomeomorph.toPartialHomeomorph X Y tX tY e) := by
  subst sX
  subst sY
  rfl

end RepulsiveCoulomb
