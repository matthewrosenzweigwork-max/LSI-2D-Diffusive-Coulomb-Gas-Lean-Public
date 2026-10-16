module

public import LeanResearch.RepulsiveCoulomb.PointConformalApproximateMidpoint
public import LeanResearch.RepulsiveCoulomb.PointConformalCompleteness
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Exact metric midpoints from compactness and verified length bisection. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace RepulsiveCoulomb

theorem proper_exists_midpoint_of_approximate {X : Type*} [MetricSpace X] [ProperSpace X]
    (happrox : ∀ x z : X, ∀ r : ℝ, dist x z / 2 < r →
      ∃ p, dist x p < r ∧ dist p z < r) (x z : X) :
    ∃ p, dist x p = dist x z / 2 ∧ dist p z = dist x z / 2 := by
  let D := dist x z
  have hD : 0 ≤ D := dist_nonneg
  have hne : (closedBall x (D + 1)).Nonempty := ⟨x, by simp [mem_closedBall]; linarith⟩
  have hc : Continuous (fun p : X ↦ max (dist x p) (dist p z)) :=
    (continuous_const.dist continuous_id).max (continuous_id.dist continuous_const)
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedBall x (D + 1)).exists_isMinOn hne hc.continuousOn
  have hbound : max (dist x p) (dist p z) ≤ D / 2 := by
    apply le_of_forall_gt
    intro r hr
    have hr' : D / 2 < min r (D + 1) := lt_min hr (by linarith)
    obtain ⟨q, hq1, hq2⟩ := happrox x z (min r (D + 1)) hr'
    have hq : q ∈ closedBall x (D + 1) := by
      rw [mem_closedBall, dist_comm]
      exact hq1.le.trans (min_le_right _ _)
    exact ((hmin hq).trans_lt (max_lt hq1 hq2)).trans_le (min_le_left _ _)
  have h1 := (le_max_left (dist x p) (dist p z)).trans hbound
  have h2 := (le_max_right (dist x p) (dist p z)).trans hbound
  have ht := dist_triangle x p z
  refine ⟨p, ?_, ?_⟩ <;> change _ = D / 2
  · change D ≤ dist x p + dist p z at ht
    linarith
  · change D ≤ dist x p + dist p z at ht
    linarith

theorem exists_pointConformal_midpoint {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    ∃ p : ℂ,
      (pointSmoothConformalEDist a y x p).toReal = (pointSmoothConformalEDist a y x z).toReal / 2 ∧
      (pointSmoothConformalEDist a y p z).toReal = (pointSmoothConformalEDist a y x z).toReal / 2 := by
  have happ : ∀ x z : ℂ, ∀ r : ℝ,
      (pointSmoothConformalEDist a y x z).toReal / 2 < r →
      ∃ p, (pointSmoothConformalEDist a y x p).toReal < r ∧
        (pointSmoothConformalEDist a y p z).toReal < r := by
    intro u v r hr
    have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
    have he : pointSmoothConformalEDist a y u v < ENNReal.ofReal r + ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add hr0.le hr0.le,
        ← ENNReal.ofReal_toReal (pointSmoothConformalEDist_lt_top ha y u v).ne]
      apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
      linarith
    obtain ⟨p, hp1, hp2⟩ := exists_pointConformal_approximate_midpoint ha y u v he
    refine ⟨p, ?_, ?_⟩
    · exact (ENNReal.toReal_lt_toReal (pointSmoothConformalEDist_lt_top ha y u p).ne ENNReal.ofReal_ne_top).mpr hp1 |>.trans_eq (ENNReal.toReal_ofReal hr0.le)
    · exact (ENNReal.toReal_lt_toReal (pointSmoothConformalEDist_lt_top ha y p v).ne ENNReal.ofReal_ne_top).mpr hp2 |>.trans_eq (ENNReal.toReal_ofReal hr0.le)
  exact @proper_exists_midpoint_of_approximate ℂ (pointSmoothConformalMetricSpace ha y)
    (pointSmoothConformalMetricSpace_proper ha y) happ x z

end RepulsiveCoulomb
