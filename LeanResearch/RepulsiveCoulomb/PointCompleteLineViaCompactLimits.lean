module

public import LeanResearch.RepulsiveCoulomb.PointAnchoredGeodesicWindows
public import LeanResearch.RepulsiveCoulomb.MetricCenteredClippedSegments
public import LeanResearch.RepulsiveCoulomb.PointGeodesicOrientedClock
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Construct an actual complete minimizing
point-metric line from opposite-endpoint segments, retaining the actual segment
witnesses and rational-time convergence needed for the curvature balance step.
This proves no side-mass balance yet; quantitative tail and cap work remains. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_complete_line_from_opposite_segments
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t : ℝ, (pointSmoothConformalEDist a y (c s) (c t)).toReal = |t - s|) ∧
      ∃ A C : ℝ, ∃ γ : ℕ → Icc (0 : ℝ) 1 → ℂ,
        ∃ τ : ℕ → Icc (0 : ℝ) 1, ∃ L : ℕ → ℝ, ∃ σ : ℕ → ℕ,
          0 < A ∧ 0 < C ∧ StrictMono σ ∧
          (∀ n : ℕ, 0 < L n ∧ ‖γ n (τ n)‖ ≤ A ∧
            γ n ⟨0, by norm_num⟩ = -(pointGeodesicWindowEndpointRadius y A C n : ℂ) ∧
            γ n ⟨1, by norm_num⟩ = (pointGeodesicWindowEndpointRadius y A C n : ℂ) ∧
            (∀ s t, (pointSmoothConformalEDist a y (γ n s) (γ n t)).toReal = |t.1 - s.1| * L n) ∧
            (n : ℝ) ≤ (τ n : ℝ) * L n ∧ (n : ℝ) ≤ (1 - (τ n : ℝ)) * L n) ∧
          ∀ q : ℚ, Tendsto
            (fun n => metricCenteredClippedSegment (γ (σ n)) (τ (σ n)) (L (σ n)) q)
            atTop (𝓝 (c q)) := by
  obtain ⟨A, C, hA, hC, hwin⟩ := exists_pointConformal_anchored_geodesic_windows ha y hB
  choose γ τ L hL hnorm h0 h1 hd hleft hright using hwin
  let d₀ : ℂ → ℝ := fun z => (pointSmoothConformalEDist a y z 0).toReal
  have hd₀ : Continuous d₀ := pointConformal_real_distance_continuous ha y 0
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall (0 : ℂ) A).exists_isMaxOn
    (show (closedBall (0 : ℂ) A).Nonempty from ⟨0, mem_closedBall_self hA.le⟩)
    hd₀.continuousOn
  let R := d₀ p
  have hanchor : ∀ n, (pointSmoothConformalEDist a y (γ n (τ n)) 0).toReal ≤ R := by
    intro n
    apply hmax
    simpa only [mem_closedBall, dist_zero_right] using hnorm n
  have hd' : ∀ n, ∀ s t : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ n s) (γ n t)).toReal =
        L n * dist (s : ℝ) t := by
    intro n s t
    rw [hd n, Real.dist_eq, abs_sub_comm]
    ring
  obtain ⟨c, hci, σ, hσ, hq⟩ := @exists_line_from_centered_finite_segments ℂ
    (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y)
    γ τ L hL hd' (0 : ℂ) R hanchor hleft hright
  have hcc := @Isometry.continuous ℝ ℂ _
    (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace c hci
  change @Continuous ℝ ℂ inferInstance
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace c at hcc
  rw [pointSmoothConformalMetricSpace_topology ha y] at hcc
  change ∀ q : ℚ, Tendsto
    (fun n => metricCenteredClippedSegment (γ (σ n)) (τ (σ n)) (L (σ n)) q)
    atTop (@nhds ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace (c q)) at hq
  rw [pointSmoothConformalMetricSpace_topology ha y] at hq
  refine ⟨c, hcc, ?_, A, C, γ, τ, L, σ, hA, hC, hσ, ?_, hq⟩
  · intro s t
    have h := @Isometry.dist_eq ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace c hci s t
    change (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t at h
    simpa only [Real.dist_eq, abs_sub_comm] using h
  · intro n
    exact ⟨hL n, hnorm n, h0 n, h1 n, hd n, hleft n, hright n⟩

end RepulsiveCoulomb
