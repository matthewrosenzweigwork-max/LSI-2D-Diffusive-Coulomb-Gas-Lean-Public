import LeanResearch.RepulsiveCoulomb.PointUnmarkedBoundaryIntrinsic
import LeanResearch.RepulsiveCoulomb.ProperBoundaryClockArclength
import LeanResearch.RepulsiveCoulomb.PointFullLinePreparationAlgebra
import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments
import LeanResearch.RepulsiveCoulomb.PlanarLineHalfplaneSides

/-! SOURCE-ONLY, UNCOMPILED. Construct the entire old minimizing boundary line
from the ambient halfplane and actual unmarked boundary coefficient data.
The input clock is purely topological and is constructed from H. It is never
assumed to be unit speed or even rectifiable. The arclength parameter is the
inverse of signed actual ambient distance after boundary convexity is proved. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- The old boundary clock determined by the actual ambient halfplane map. -/
def pointHalfplaneBoundaryClock (H : ℂ ≃ₜ ℂ) (t : ℝ) : ℂ := H.symm (t : ℂ)

/-- All topology here is literal ambient topology. No metric property of H is
asserted or used. -/
theorem pointHalfplaneBoundaryClock_properties
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane) :
    IsClosed P ∧ IsClosedEmbedding (pointHalfplaneBoundaryClock H) ∧
      range (pointHalfplaneBoundaryClock H) = frontier P ∧
      IsPreconnected (frontier P) := by
  have hclosed : IsClosed P := by
    rw [hP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hβ : IsClosedEmbedding (pointHalfplaneBoundaryClock H) :=
    H.symm.isClosedEmbedding.comp Complex.isometry_ofReal.isClosedEmbedding
  have hfront : frontier P = H ⁻¹' {z : ℂ | z.im = 0} := by
    rw [hP, ← H.preimage_frontier]
    exact congrArg (fun S : Set ℂ ↦ H ⁻¹' S) (Complex.frontier_setOfPred_le_im 0)
  have hrange : range (pointHalfplaneBoundaryClock H) = frontier P := by
    rw [hfront]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      simp [pointHalfplaneBoundaryClock]
    · intro hz
      refine ⟨(H z).re, ?_⟩
      have he : ((H z).re : ℂ) = H z := by
        apply Complex.ext
        · simp
        · simpa only [Complex.ofReal_im] using hz.symm
      simp only [pointHalfplaneBoundaryClock, he, H.symm_apply_apply]
  have hconn : IsPreconnected (frontier P) := by
    rw [← hrange, ← image_univ]
    exact isPreconnected_univ.image _ hβ.continuous.continuousOn
  exact ⟨hclosed, hβ, hrange, hconn⟩

/-- Unmarkedness refers to the actual union of the two Finsupp supports.
It forces physical retained width pi, not zero ambient cone exponent. -/
theorem pointUnmarkedBoundary_flat_charts
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ}
    {turn : ℂ → ℝ} {ν α : ℂ →₀ ℝ}
    (hturn : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      turn p = Real.pi - C.flatPhysicalWidth)
    (hν : PointFullStripCurvatureRepresentation a y P turn ν)
    (hclean : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P)) :
    ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      C.flatPhysicalWidth = Real.pi := by
  intro p hp
  obtain ⟨C, hC⟩ := hturn p hp
  have ht : turn p = 0 := by
    by_contra hn
    exact disjoint_left.mp hclean (hν.boundary_marked α p hp hn) hp
  exact ⟨C, by rw [ht] at hC; linarith⟩

/-- The complete all-real ambient-minimizing line is now a constructed output.
The parameter identity specifies the new arclength clock at every old clock
point, and range equality includes the ENTIRE old frontier. -/
theorem point_exists_unmarked_complete_boundary_line
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (turn : ℂ → ℝ)
    (hturn : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      turn p = Real.pi - C.flatPhysicalWidth)
    (ν α : ℂ →₀ ℝ)
    (hν : PointFullStripCurvatureRepresentation a y P turn ν)
    (hclean : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P)) :
    ∃ line : ℝ → ℂ,
      (∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t) ∧
      frontier P = range line ∧ Function.Injective line ∧
      IsClosedEmbedding line ∧ IsProperMap line ∧
      ∀ t : ℝ, line (@ProperBoundaryClock.signedDistance ℂ
        (pointSmoothConformalMetricSpace ha y) (pointHalfplaneBoundaryClock H) t) =
          pointHalfplaneBoundaryClock H t := by
  obtain ⟨hclosed, hβ, hrange, hconn⟩ := pointHalfplaneBoundaryClock_properties H hP
  have hflat := pointUnmarkedBoundary_flat_charts hturn hν hclean
  have hconv := pointBoundaryFlat_geodesicallyConvex ha y hclosed hconn hflat
  have hβ' : @IsClosedEmbedding ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (pointHalfplaneBoundaryClock H) := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hsegments : @ProperBoundaryClock.HasContainedMinimizingSegments ℂ
      (pointSmoothConformalMetricSpace ha y) (pointHalfplaneBoundaryClock H) := by
    intro s t
    have hs : pointHalfplaneBoundaryClock H s ∈ frontier P := hrange ▸ mem_range_self s
    have ht : pointHalfplaneBoundaryClock H t ∈ frontier P := hrange ▸ mem_range_self t
    obtain ⟨γ, h0, h1, hc, hfront, hd⟩ := hconv _ hs _ ht
    have hc' : @Continuous unitInterval ℂ _
        (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
      rwa [pointSmoothConformalMetricSpace_topology ha y]
    refine ⟨γ, hc', h0, h1, ?_, ?_⟩
    · rintro z ⟨u, rfl⟩
      rw [hrange]
      exact hfront u
    · intro u v
      change (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
        |u.1 - v.1| * (pointSmoothConformalEDist a y
          (pointHalfplaneBoundaryClock H s) (pointHalfplaneBoundaryClock H t)).toReal
      simpa only [abs_sub_comm] using hd u v
  obtain ⟨line, hline, hlineRange, hparam⟩ :=
    @ProperBoundaryClock.exists_isometry_range_eq_of_contained_segments ℂ
      (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y)
      (pointHalfplaneBoundaryClock H) hβ' hsegments
  have hd : ∀ s t, (pointSmoothConformalEDist a y (line s) (line t)).toReal = dist s t :=
    @Isometry.dist_eq ℝ ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace line hline
  have he := pointMetricLine_isClosedEmbedding ha y line hd
  exact ⟨line, hd, hrange.symm.trans hlineRange.symm, he.injective,
    he, he.isProperMap, hparam⟩

end RepulsiveCoulomb
