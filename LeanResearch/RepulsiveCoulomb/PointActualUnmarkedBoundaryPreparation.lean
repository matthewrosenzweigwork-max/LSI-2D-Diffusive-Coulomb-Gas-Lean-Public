module

public import LeanResearch.RepulsiveCoulomb.PointUnmarkedBoundaryLine
public import LeanResearch.RepulsiveCoulomb.PointActualFullLinePreparation

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Original-input preliminary full-strip preparation.
The former entire-frontier minimizing-line hypothesis has been removed: that
line and its real arclength parametrization are constructed from the actual
ambient halfplane, genuine boundary charts and unmarked finite coefficients.
No additional strip, continuation family, line certificate, or regular ambient
exponent hypothesis appears. The output is the existing actual cut package. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- The preliminary case of the cutting argument, now from the original
geometric/finite-coefficient input. All first-contact, literal residual,
ambient curvature equality, support/rank, and clean-budget-ray conclusions are
those of the constructed `PointFullLinePreparationStep`. -/
theorem point_exists_actual_unmarked_boundary_preparation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (turn : ℂ → ℝ)
    (hturn : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      turn p = Real.pi - C.flatPhysicalWidth)
    (ν α : ℂ →₀ ℝ)
    (hν : PointFullStripCurvatureRepresentation a y P turn ν)
    (hαP : (↑α.support : Set ℂ) ⊆ P)
    (hbudget : PointSignedBudgetInvariant ν α)
    (hclean : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P)) :
    ∃ line : ℝ → ℂ,
      (∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t) ∧
      frontier P = range line ∧ Function.Injective line ∧
      IsClosedEmbedding line ∧ IsProperMap line ∧
      (∀ t : ℝ, line (@ProperBoundaryClock.signedDistance ℂ
        (pointSmoothConformalMetricSpace ha y) (pointHalfplaneBoundaryClock H) t) =
          pointHalfplaneBoundaryClock H t) ∧
      Nonempty (PointFullLinePreparationStep a y P line ν α) := by
  obtain ⟨line, hd, hrange, hinj, hclosed, hproper, hclock⟩ :=
    point_exists_unmarked_complete_boundary_line ha y H hHP turn hturn ν α hν hclean
  exact ⟨line, hd, hrange, hinj, hclosed, hproper, hclock,
    point_exists_actual_full_line_preparation ha y H hHP line hd hrange
      turn hturn ν α hν hαP hbudget hclean⟩

end RepulsiveCoulomb
