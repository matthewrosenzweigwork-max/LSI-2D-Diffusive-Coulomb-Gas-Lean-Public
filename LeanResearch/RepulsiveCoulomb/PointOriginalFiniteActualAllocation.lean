import LeanResearch.RepulsiveCoulomb.PointFiniteActualPreparation
import LeanResearch.RepulsiveCoulomb.PointOriginalActualCutPrefix

/-! SOURCE-ONLY, UNCOMPILED. Total finite actual allocation from the genuine
original halfplane inputs. The existing honest prefix type and all its sector
geometry are retained unchanged. The new builder always produces a completed
prefix by supplying the constructed total inner preparation at every outer
step. Terminal zero budget requires no residual region or coverage assertion.
This is finite sector allocation, not the subsequent global surgery theorem. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Strong outer-rank recursion with an actual total preparation at every
current state. No marked-boundary blocker constructor is used. -/
theorem point_construct_completed_actual_cut_prefix
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) :
    ∃ T : PointFiniteActualCutPrefix a y K, T.completed := by
  classical
  have build : ∀ n : ℕ, ∀ (P : Set ℂ) (ν α : ℂ →₀ ℝ)
      (K : PointGeometricCutState a y P ν α), pointCutOuterRank P ν α = n →
        ∃ T : PointFiniteActualCutPrefix a y K, T.completed := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P ν α K hn
      obtain ⟨B⟩ := K.prepare_total ha y
      obtain ⟨S, hterminal | hnext⟩ := B.state.construct_sector_and_step ha y B.clean
      · exact ⟨.terminal K B S hterminal.2, trivial⟩
      · obtain ⟨O⟩ := hnext
        have hd : pointCutOuterRank O.Q O.curvature (retainedApexBudget α S.apex S.beta) < n :=
          hn ▸ O.rank_lt.trans_le B.rank_le
        obtain ⟨tail, htail⟩ := ih _ hd _ _ _ O.state rfl
        exact ⟨.next K B S O tail, htail⟩
  exact build _ P ν α K rfl

/-- The full original-input allocation endpoint. The finite boundary pieces,
ambient halfplane identity, coefficient meanings and signed invariant are
genuine initial data. Rays, strips, sectors, transitions, termination and the
final allocation are all constructed, not new hypotheses. -/
theorem point_original_halfplane_finite_actual_allocation
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
      T.completed ∧
      T.sectors.length ≤ pointCutOuterRank P ν α + 1 ∧
      (∀ S ∈ T.sectors, S.apex ∈ α.support) ∧
      (∀ S ∈ T.sectors, range S.map ⊆ P) ∧
      (∀ S ∈ T.sectors, S.openImage ⊆ interior P) ∧
      T.sectors.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      T.remaining = 0 ∧
      pointActualAllocatedBudget T.sectors = α ∧
      (∀ p : ℂ, pointActualAllocatedBudget T.sectors p = α p) := by
  let K := PointGeometricCutState.ofOriginal ha H hHP hνoff hνint hνboundary
    hαP hbudget pieces hpieces
  obtain ⟨T, hT⟩ := point_construct_completed_actual_cut_prefix ha y K
  have he := T.exact_allocation_of_completed hT
  exact ⟨T, hT, T.length_le_rank_add_one, T.selected_apex_supported,
    T.selected_range_subset, T.selected_openImage_subset,
    T.pairwise_disjoint_openImages, T.remaining_zero_of_completed hT, he,
    fun p ↦ congrArg (fun b : ℂ →₀ ℝ ↦ b p) he⟩

/-- List-only family interface for subsequent finite sector surgery. Each
entry itself contains the positive angle at most pi and the actual ambient
all-pairs sector metric identity; no metric or local geometry is erased. -/
theorem PointGeometricCutState.exists_finite_actual_allocation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) :
    ∃ L : List (PointActualAllocatedSector a y),
      L.length ≤ pointCutOuterRank P ν α + 1 ∧
      (∀ S ∈ L, S.apex ∈ α.support) ∧
      (∀ S ∈ L, range S.map ⊆ P) ∧
      (∀ S ∈ L, S.openImage ⊆ interior P) ∧
      L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      pointActualAllocatedBudget L = α := by
  obtain ⟨T, hT⟩ := point_construct_completed_actual_cut_prefix ha y K
  exact ⟨T.sectors, T.length_le_rank_add_one, T.selected_apex_supported,
    T.selected_range_subset, T.selected_openImage_subset,
    T.pairwise_disjoint_openImages, T.exact_allocation_of_completed hT⟩

end RepulsiveCoulomb
