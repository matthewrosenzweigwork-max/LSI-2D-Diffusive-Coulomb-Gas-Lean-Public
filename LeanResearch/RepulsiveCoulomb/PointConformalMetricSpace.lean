import LeanResearch.RepulsiveCoulomb.PointConformalPathBarrier

/-! A genuine finite metric structure built from the smooth-path conformal distance.
This is deliberately not a global instance on the ambient complex plane: equality
of its topology with the Euclidean topology, completeness, and equivalence with the
manuscript's all-rectifiable-curve metric remain separate proof obligations. -/
noncomputable section
open scoped ENNReal
namespace RepulsiveCoulomb

@[instance_reducible] def pointSmoothConformalEMetricSpace {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : EMetricSpace ℂ where
  edist := pointSmoothConformalEDist a y
  edist_self := pointSmoothConformalEDist_self a y
  edist_comm := pointSmoothConformalEDist_comm a y
  edist_triangle := pointSmoothConformalEDist_triangle a y
  eq_of_edist_eq_zero := fun h ↦ (pointSmoothConformalEDist_eq_zero_iff ha y _ _).mp h

@[instance_reducible] def pointSmoothConformalMetricSpace {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : MetricSpace ℂ :=
  letI := pointSmoothConformalEMetricSpace ha y
  EMetricSpace.toMetricSpace (fun x z ↦ (pointSmoothConformalEDist_lt_top ha y x z).ne)

theorem pointSmoothConformalMetricSpace_dist {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    @dist ℂ (pointSmoothConformalMetricSpace ha y).toDist x z =
      (pointSmoothConformalEDist a y x z).toReal := rfl

end RepulsiveCoulomb
