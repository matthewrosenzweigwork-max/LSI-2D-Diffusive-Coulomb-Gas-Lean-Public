import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments
import LeanResearch.RepulsiveCoulomb.PointGeodesicOrientedClock
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Uncompiled additive successor. Actual point-metric lines escape Euclidean
compact sets. Actual finite segments can meet a fixed Euclidean disk only in a
uniformly bounded centered metric-time window. -/
noncomputable section
open Set Filter Metric Topology
namespace RepulsiveCoulomb

theorem pointMetricLine_norm_tendsto_atTop
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) :
    Tendsto (fun t => ‖c t‖) atTop atTop := by
  have hproper := (pointMetricLine_isClosedEmbedding ha y c hd).tendsto_cocompact
  have htop : Tendsto c atTop (cocompact ℂ) := hproper.mono_left atTop_le_cocompact
  exact tendsto_norm_cocompact_atTop.comp htop

theorem pointMetricLine_norm_tendsto_atBot
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) :
    Tendsto (fun t => ‖c t‖) atBot atTop := by
  have hproper := (pointMetricLine_isClosedEmbedding ha y c hd).tendsto_cocompact
  have hbot : Tendsto c atBot (cocompact ℂ) := hproper.mono_left atBot_le_cocompact
  exact tendsto_norm_cocompact_atTop.comp hbot

theorem exists_pointConformal_disk_distance_bound
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, ‖z‖ ≤ A → (pointSmoothConformalEDist a y z 0).toReal ≤ R := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall (0 : ℂ) A).exists_isMaxOn
    (show (closedBall (0 : ℂ) A).Nonempty from ⟨0, mem_closedBall_self hA⟩)
    (pointConformal_real_distance_continuous ha y 0).continuousOn
  refine ⟨(pointSmoothConformalEDist a y p 0).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro z hz
  apply hmax
  simpa only [mem_closedBall, dist_zero_right] using hz

theorem pointConformal_geodesic_two_disk_parameters_bound
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (L : ℝ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * L)
    {A R : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ ≤ A → (pointSmoothConformalEDist a y z 0).toReal ≤ R)
    (s t : Icc (0 : ℝ) 1) (hs : ‖γ s‖ ≤ A) (ht : ‖γ t‖ ≤ A) :
    |t.1 - s.1| * L ≤ 2 * R := by
  have htri := @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    (γ s) 0 (γ t)
  change (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤
    (pointSmoothConformalEDist a y (γ s) 0).toReal +
      (pointSmoothConformalEDist a y 0 (γ t)).toReal at htri
  rw [pointSmoothConformalEDist_comm a y 0 (γ t), hd] at htri
  linarith [hbound (γ s) hs, hbound (γ t) ht]

theorem pointConformal_centered_parameter_after_disk_crossing
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) {L : ℝ} (hL : 0 < L)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = |t.1 - s.1| * L)
    {A R q : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ ≤ A → (pointSmoothConformalEDist a y z 0).toReal ≤ R)
    (τ s : Icc (0 : ℝ) 1) (hτs : τ ≤ s) (hτ : ‖γ τ‖ ≤ A) (hs : ‖γ s‖ ≤ A)
    (hq : 2 * R < q) : (s : ℝ) < (τ : ℝ) + q / L := by
  have h := pointConformal_geodesic_two_disk_parameters_bound ha y γ L hd hbound τ s hτ hs
  rw [abs_of_nonneg (sub_nonneg.mpr (show (τ : ℝ) ≤ s from hτs))] at h
  have hquot : (s : ℝ) - τ < q / L := (lt_div_iff₀ hL).mpr (by linarith)
  linarith

end RepulsiveCoulomb
