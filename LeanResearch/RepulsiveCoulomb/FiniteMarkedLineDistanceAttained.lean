module

public import LeanResearch.RepulsiveCoulomb.PointConformalCompleteness
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Isometry

@[expose] public section

/-! Source-only, uncompiled. The finite nonempty marked set and the actual
complete metric line produce the minimum. No distance-attainment field is used. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem finite_marked_isometric_line_distance_attained
    {Y : Type*} [MetricSpace Y] [ProperSpace Y]
    (line : ℝ → Y) (hline : Isometry line)
    {S : Set Y} (hS : S.Finite) (hne : S.Nonempty)
    (hclean : Disjoint S (range line)) :
    ∃ h : ℝ, 0 < h ∧ ∃ x ∈ S, ∃ r : ℝ,
      dist x (line r) = h ∧ ∀ p ∈ S, ∀ t : ℝ, h ≤ dist p (line t) := by
  have hclosed : IsClosed (range line) := hline.isClosedEmbedding.isClosed_range
  have hLne : (range line).Nonempty := ⟨line 0, mem_range_self 0⟩
  obtain ⟨x, hx, hmin⟩ := hS.isCompact.exists_isMinOn hne
    (continuous_infDist_pt (range line)).continuousOn
  obtain ⟨z, hz, he⟩ := hclosed.exists_infDist_eq_dist hLne x
  obtain ⟨r, rfl⟩ := hz
  have hxne : x ≠ line r := by
    intro heq
    exact disjoint_left.mp hclean hx (heq.symm ▸ mem_range_self r)
  refine ⟨dist x (line r), dist_pos.mpr hxne, x, hx, r, rfl, ?_⟩
  intro p hp t
  rw [← he]
  exact (hmin hp).trans (infDist_le_dist_of_mem (mem_range_self t))

theorem pointMarkedLine_distance_attained
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    {S : Set ℂ} (hS : S.Finite) (hne : S.Nonempty)
    (hclean : Disjoint S (range line)) :
    ∃ h : ℝ, 0 < h ∧ ∃ x ∈ S, ∃ r : ℝ,
      (pointSmoothConformalEDist a y x (line r)).toReal = h ∧
      ∀ p ∈ S, ∀ t : ℝ, h ≤ (pointSmoothConformalEDist a y p (line t)).toReal := by
  let M := pointSmoothConformalMetricSpace ha y
  have hLine : @Isometry ℝ ℂ inferInstance M.toPseudoEMetricSpace line :=
    @Isometry.of_dist_eq ℝ ℂ inferInstance M.toPseudoMetricSpace line hline
  exact @finite_marked_isometric_line_distance_attained ℂ M
    (pointSmoothConformalMetricSpace_proper ha y) line hLine S hS hne hclean

end RepulsiveCoulomb
