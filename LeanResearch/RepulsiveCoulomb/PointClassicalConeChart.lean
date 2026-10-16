module

public import LeanResearch.RepulsiveCoulomb.LocalIsometryBall
public import LeanResearch.RepulsiveCoulomb.PointConformalMetricCharts

@[expose] public section

/-! Actual local charts into the classical cone metric, with intrinsic radial
coordinates. Coincident exponents are merged and zero-exponent points remain flat. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

@[instance_reducible] def pointClassicalConeMetricSpace {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (p : ℂ) : MetricSpace ℂ :=
  classicalConeMetricSpace (coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))

def pointClassicalConeDist {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p u v : ℂ) : ℝ :=
  @dist ℂ (pointClassicalConeMetricSpace a y p).toDist u v

theorem pointClassicalConeMetricSpace_topology {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (p : ℂ) :
    (pointClassicalConeMetricSpace a y p).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := classicalConeMetricSpace_topology _ _

theorem exists_pointConformal_classical_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      ∀ u ∈ e.source, ∀ v ∈ e.source,
        (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (e u) (e v) := by
  obtain ⟨e, r, hr, hep, hsub, hd⟩ := exists_pointConformal_cone_metric_chart ha y p
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  let eR := e.restrOpen (ball p r) isOpen_ball
  let f := eR.trans (coneRadialHomeomorph α hα).toOpenPartialHomeomorph
  have hsource : f.source = e.source ∩ ball p r := by
    simp [f, eR]
  have hf (u : ℂ) : f u = coneRadialEquiv α hα (e u) := rfl
  have hpball : p ∈ ball p r := mem_ball_self hr
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hsource]
    exact ⟨hsub hpball, hpball⟩
  · rw [hf, hep, coneRadialEquiv_zero]
  · intro u hu v hv
    rw [hsource] at hu hv
    rw [hf, hf]
    change (pointSmoothConformalEDist a y u v).toReal =
      (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations
        ((coneRadialEquiv α hα).symm (coneRadialEquiv α hα (e u)))
        ((coneRadialEquiv α hα).symm (coneRadialEquiv α hα (e v)))).toReal
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hd u hu.2 v hv.2]

end RepulsiveCoulomb
