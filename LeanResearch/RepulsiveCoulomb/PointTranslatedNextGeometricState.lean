import LeanResearch.RepulsiveCoulomb.PointAttainedTranslatedResidual
import LeanResearch.RepulsiveCoulomb.PointGeometricCutState

/-! SOURCE-ONLY, UNCOMPILED. Repackage the ACTUALLY constructed translated
residual as the same current-state type used by finite preparation recursion.
The finite old-piece restriction theorem constructs its new frontier cover;
no future stage, clean ray or rank decrease is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb.PointTranslatedStripIterationOutput
variable {m N : ℕ} {a : Fin m→ℝ} {y : Fin m→ℂ}
  {P S Q : Set ℂ} {τ : NNReal→ℂ} {p : ℂ} {ν μ α : ℂ→₀ℝ} {θ : ℝ}
  {Cz : PointRetainedConeNeighborhood a y P (τ 0)}

theorem exists_next_geometric_state
    (O : PointTranslatedStripIterationOutput a y P S Q τ p ν μ α θ Cz)
    (ha : ∀ j,0≤a j) (hP : IsClosed P)
    (old : Fin N→PointClosedBoundaryGeodesicPiece a y)
    (hold : frontier P=⋃ i,range (old i).curve)
    (hbudget : PointSignedBudgetInvariant ν α) :
    ∃ K : PointGeometricCutState a y Q μ α,
      K.toPointRetainedSignedHalfplaneState=O.state ∧ K.pieceCount=N+1 := by
  obtain ⟨fresh,hfresh⟩ := O.exists_finite_boundary_cover ha hP old hold
  refine ⟨{
    toPointRetainedSignedHalfplaneState := O.state
    budget := O.budget_invariant hbudget
    pieceCount := N+1
    pieces := fresh
    boundary_cover := hfresh },rfl,rfl⟩

end RepulsiveCoulomb.PointTranslatedStripIterationOutput
