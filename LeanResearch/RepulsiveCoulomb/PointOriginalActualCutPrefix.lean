import LeanResearch.RepulsiveCoulomb.PointFiniteActualCutGeometry

/-! SOURCE-ONLY, UNCOMPILED. Original geometric input endpoint for the finite
actual prefix. Genuine current-region hypotheses are unchanged. The output is
explicitly permitted to end at the remaining translated-strip preparation
obstruction; there is no claim that the full Bonk--Lang allocation is proved.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Construct a finite actual prefix from the original halfplane hypotheses,
without requiring the caller to supply a state, a sector, a clean ray, an
induction family, move existence, angle allocations, or desired termination. -/
theorem point_original_halfplane_finite_actual_cut_prefix
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (ν α : ℂ →₀ ℝ) (hbudget : PointSignedBudgetInvariant ν α)
    (hνoff : ∀ x, x ∉ P → ν x = 0)
    (hνint : ∀ x ∈ interior P, ν x = -Real.pi * coalescedPointExponent a y x)
    (hνboundary : ∀ x ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P x,
      ν x = Real.pi - C.flatPhysicalWidth ∧ C.Admissible)
    (hαP : ∀ x, α x ≠ 0 → x ∈ P) :
    let K := PointGeometricCutState.ofOriginal ha H hHP hνoff hνint hνboundary
      hαP hbudget pieces hpieces
    ∃ T : PointFiniteActualCutPrefix a y K,
      T.sectors.length ≤ pointCutOuterRank P ν α + 1 ∧
      (∀ S ∈ T.sectors, S.apex ∈ α.support) ∧
      (∀ S ∈ T.sectors, range S.map ⊆ P) ∧
      (∀ S ∈ T.sectors, S.openImage ⊆ interior P) ∧
      T.sectors.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      α = pointActualAllocatedBudget T.sectors + T.remaining ∧
      ((T.completed ∧ pointActualAllocatedBudget T.sectors = α) ∨
       (∃ (Q : Set ℂ) (μ : ℂ →₀ ℝ) (L : PointGeometricCutState a y Q μ T.remaining),
         (∃ x, x ∈ pointSignedMarked μ T.remaining ∧ x ∈ frontier Q) ∧
         ¬Nonempty L.CleanRay)) := by
  classical
  let K := PointGeometricCutState.ofOriginal ha H hHP hνoff hνint hνboundary
    hαP hbudget pieces hpieces
  obtain ⟨T⟩ := point_construct_finite_actual_cut_prefix ha y K
  refine ⟨T, T.length_le_rank_add_one, T.selected_apex_supported,
    T.selected_range_subset, T.selected_openImage_subset,
    T.pairwise_disjoint_openImages, T.budget_balance, ?_⟩
  by_cases h : T.completed
  · exact Or.inl ⟨h, T.exact_allocation_of_completed h⟩
  · exact Or.inr (T.obstruction_of_not_completed h)

end RepulsiveCoulomb
