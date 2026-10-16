import LeanResearch.RepulsiveCoulomb.PointActualTranslatedStripIteration
import LeanResearch.RepulsiveCoulomb.PointRetainedSectorFiniteBoundaryCoverClassical

/-! SOURCE-ONLY MAXIMAL-WIDTH ADAPTER. The actual translated residual has a
finite genuine minimizing-piece boundary cover. This uses the cut's constructed
ambient convexity and literal frontier, and the generic old-piece restriction
theorem; no entire bent boundary is treated as a minimizing geodesic. -/
noncomputable section
open Set
namespace RepulsiveCoulomb.PointTranslatedStripIterationOutput

variable {m N:ℕ} {a:Fin m→ℝ} {y:Fin m→ℂ}
    {P S Q:Set ℂ} {τ:NNReal→ℂ} {p:ℂ} {ν μ α:ℂ→₀ℝ} {θ:ℝ}
    {Cz:PointRetainedConeNeighborhood a y P (τ 0)}

theorem exists_finite_boundary_cover
    (D:PointTranslatedStripIterationOutput a y P S Q τ p ν μ α θ Cz)
    (ha:∀j,0≤a j) (hP:IsClosed P)
    (old:Fin N→PointClosedBoundaryGeodesicPiece a y)
    (hold:frontier P=⋃i,range (old i).curve) :
    ∃fresh:Fin (N+1)→PointClosedBoundaryGeodesicPiece a y,
      frontier Q=⋃i,range (fresh i).curve := by
  apply pointRetainedSector_construct_finite_boundary_cover_classical ha y hP D.state.isClosed
    D.subset_old (D.state.intrinsic_eq_and_geodesicallyConvex ha).1 old hold τ D.top_metric D.top_frontier
  intro x hx
  rw [D.frontier_eq] at hx
  rcases hx with hx|hx
  · exact Or.inl hx
  · right
    rw [D.old_forward_range] at hx
    rcases hx with hx|hx
    · simpa only [hx] using D.origin_old_frontier
    · exact hx.1

end RepulsiveCoulomb.PointTranslatedStripIterationOutput
