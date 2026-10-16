import LeanResearch.RepulsiveCoulomb.PointBalancedSideInitialState
import LeanResearch.RepulsiveCoulomb.PointFiniteSectorLocalGeometry

/-! SOURCE-ONLY, UNCOMPILED. Finite actual allocation on the original plane.
Both sides are constructed from ha,y, allocated by the completed halfplane
recursion, then concatenated. No chart, state, certificate, balancing result,
sector coverage, surgery metric or global developing map is an input. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

@[simp] theorem pointActualAllocatedBudget_append
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L M : List (PointActualAllocatedSector a y)) :
    pointActualAllocatedBudget (L ++ M) = pointActualAllocatedBudget L + pointActualAllocatedBudget M := by
  induction L with
  | nil => simp [pointActualAllocatedBudget]
  | cons S L ih =>
    change Finsupp.single S.apex S.beta + pointActualAllocatedBudget (L ++ M) =
      (Finsupp.single S.apex S.beta + pointActualAllocatedBudget L) + pointActualAllocatedBudget M
    rw [ih, add_assoc]

/-- Positive mass: the two completed geometric recursions supply the actual
finite list and its interior regularity. Opposite-side disjointness follows
from containment in the two original open sides, not from a seam assumption. -/
theorem point_original_plane_finite_actual_allocation_positive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ L : List (PointActualAllocatedSector a y),
      L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      (∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
        z.1 ∈ interior (closedEuclideanSector S.beta) →
          coalescedPointExponent a y (S.map z) = 0) ∧
      ∀ p, (1 - 1/(1+pointExteriorHalfMass a)) * pointActualAllocatedBudget L p =
        Real.pi * coalescedPointExponent a y p := by
  classical
  obtain ⟨D⟩ := exists_pointBalancedInitialStates ha y hB
  obtain ⟨T, hT⟩ := point_construct_completed_actual_cut_prefix ha y D.leftState
  obtain ⟨U, hU⟩ := point_construct_completed_actual_cut_prefix ha y D.rightState
  refine ⟨T.sectors ++ U.sectors, ?_, ?_, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨T.pairwise_disjoint_openImages, U.pairwise_disjoint_openImages, ?_⟩
    intro S hS E hE
    exact D.disjoint_interiors.mono
      (T.selected_openImage_subset S hS) (U.selected_openImage_subset E hE)
  · intro S hS
    rcases List.mem_append.mp hS with hS | hS
    · exact T.selected_interior_regular S hS
    · exact U.selected_interior_regular S hS
  · intro p
    rw [pointActualAllocatedBudget_append, T.exact_allocation_of_completed hT,
      U.exact_allocation_of_completed hU, Finsupp.add_apply]
    exact D.cancellation p

/-- Literal zero-mass branch: every exponent vanishes; the allocation is the
empty list and the identity already has the original metric. No division by
zero is used in a signed-budget state and no positive budget is fabricated. -/
theorem point_original_plane_zero_mass_identity
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : pointExteriorHalfMass a = 0) :
    (∀ p, coalescedPointExponent a y p = 0) ∧
    pointActualAllocatedBudget ([] : List (PointActualAllocatedSector a y)) = 0 ∧
    (∀ x z, pointRectifiableConformalEDist a y x z = ENNReal.ofReal ‖z-x‖) ∧
    ∃ F : ℂ ≃ₜ ℂ, F = Homeomorph.refl ℂ ∧
      ∀ x z, ‖F z - F x‖ = (pointRectifiableConformalEDist a y x z).toReal := by
  have hsum : ∑ j, a j = 0 := by
    have h := hB
    unfold pointExteriorHalfMass at h
    rw [← Finset.sum_div] at h
    linarith
  have hz : ∀ j, a j = 0 := pointExponent_eq_zero_of_sum_zero ha hsum
  refine ⟨?_, rfl, pointRectifiableConformalEDist_eq_euclidean_of_sum_zero ha hsum y, ?_⟩
  · intro p
    simp [coalescedPointExponent, hz]
  · refine ⟨Homeomorph.refl ℂ, rfl, ?_⟩
    intro x z
    change ‖z-x‖ = (pointRectifiableConformalEDist a y x z).toReal
    rw [pointRectifiableConformalEDist_eq_euclidean_of_sum_zero ha hsum y,
      ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Original-input all-masses endpoint for finite sector surgery. The zero
case is literally empty. Positive mass uses actual constructed halfplanes.
This theorem does not assert existence of the later global surgery map. -/
theorem point_original_plane_finite_actual_allocation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ c : ℝ, ∃ L : List (PointActualAllocatedSector a y),
      c = 1/(1+pointExteriorHalfMass a) ∧ 0 < c ∧ c ≤ 1 ∧
      L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      (∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
        z.1 ∈ interior (closedEuclideanSector S.beta) →
          coalescedPointExponent a y (S.map z) = 0) ∧
      (∀ p, (1-c) * pointActualAllocatedBudget L p = Real.pi * coalescedPointExponent a y p) ∧
      (pointExteriorHalfMass a = 0 → L = []) := by
  have hBnonneg : 0 ≤ pointExteriorHalfMass a := by
    unfold pointExteriorHalfMass
    exact Finset.sum_nonneg (fun j _ ↦ div_nonneg (ha j) (by norm_num))
  have hden : 0 < 1+pointExteriorHalfMass a := by linarith
  have hcpos : 0 < 1/(1+pointExteriorHalfMass a) := div_pos zero_lt_one hden
  have hcle : 1/(1+pointExteriorHalfMass a) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  by_cases hB : 0 < pointExteriorHalfMass a
  · obtain ⟨L, hdis, hregular, hcancel⟩ :=
      point_original_plane_finite_actual_allocation_positive ha y hB
    exact ⟨_, L, rfl, hcpos, hcle, hdis, hregular, hcancel,
      fun hz ↦ False.elim (hB.ne' hz)⟩
  · have hz : pointExteriorHalfMass a = 0 := le_antisymm (le_of_not_gt hB) hBnonneg
    obtain ⟨hκ, _, _, _⟩ := point_original_plane_zero_mass_identity ha y hz
    refine ⟨_, [], rfl, hcpos, hcle, List.Pairwise.nil, ?_, ?_, fun _ ↦ rfl⟩
    · simp
    · intro p
      simp [pointActualAllocatedBudget, hκ]

end RepulsiveCoulomb
