module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorEndpointDichotomy
public import LeanResearch.RepulsiveCoulomb.PointActualUnmarkedBoundaryPreparation

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Close the original unmarked-boundary preparation
branch and preserve every current-state invariant, including a genuine finite
geodesic boundary cover and an actual clean budget ray. No complete-line or
preparation certificate is supplied. The marked, unprepared branch is left
explicit rather than replaced by an assumed next-move theorem.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

structure PointConstructedPreparation {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (ν α : ℂ →₀ ℝ) where
  Q : Set ℂ
  curvature : ℂ →₀ ℝ
  state : PointGeometricCutState a y Q curvature α
  clean : state.CleanRay
  subset_old : Q ⊆ P
  curvature_mass : pointSignedCurvatureMass curvature α = pointSignedCurvatureMass ν α
  negative_nonincrease : ∀ x, signedBudgetNeg (curvature x) ≤ signedBudgetNeg (ν x)
  interior_unchanged : ∀ x ∈ interior Q, curvature x = ν x
  rank_le : pointCutOuterRank Q curvature α ≤ pointCutOuterRank P ν α

theorem pointCutOuterRank_le_of_preparation_coefficients
    {P Q : Set ℂ} {ν μ α : ℂ →₀ ℝ} (hQP : Q ⊆ P)
    (hi : ∀ x ∈ interior Q, μ x = ν x) :
    pointCutOuterRank Q μ α ≤ pointCutOuterRank P ν α := by
  have hA : pointSignedBudgetMass μ α = pointSignedBudgetMass ν α := by
    rw [pointSignedBudgetMass_eq_support_sum, pointSignedBudgetMass_eq_support_sum]
  have hcard := Finset.card_le_card (pointCutInteriorMarks_subset (α := α) (δ := α) hQP hi (fun _ _ ↦ rfl))
  unfold pointCutOuterRank
  rw [hA]
  omega

/-- A full strip's actual top line supplies the entire finite geodesic cover
(one piece), including the retained singular ambient points of intrinsic
boundary width pi. No old whole-frontier geodesic premise survives. -/
theorem PointFullLinePreparationStep.to_actual_preparation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {line : ℝ → ℂ} {ν α : ℂ →₀ ℝ}
    (R : PointFullLinePreparationStep a y P line ν α) :
    Nonempty (PointConstructedPreparation a y P ν α) := by
  let top : ℝ → ℂ := fun t ↦ (R.strip (fullStripTop R.height_pos.le t)).1
  let E : PointClosedBoundaryGeodesicPiece a y :=
    { interval := univ, interval_closed := isClosed_univ, interval_convex := convex_univ,
      curve := fun t ↦ top t.1, metric := fun s t ↦ R.top_metric s.1 t.1 }
  have hrange : range E.curve = range top := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨t, mem_univ _⟩, rfl⟩
  have hcover : frontier R.Q = ⋃ _i : Fin 1, range E.curve := by
    simpa only [iUnion_const] using R.frontier_eq.trans hrange.symm
  have hboundary : ∀ x ∈ frontier R.Q, ∃ C : PointRetainedConeNeighborhood a y R.Q x,
      R.νQ x = Real.pi - C.flatPhysicalWidth ∧ C.Admissible := by
    intro x hx
    obtain ⟨t, rfl⟩ := R.frontier_eq ▸ hx
    obtain ⟨C, _, hturn, hC⟩ := R.top_retained t
    exact ⟨C, (R.νQ_representation.boundary_eq _ hx).trans hturn.symm, hC⟩
  let K : PointGeometricCutState a y R.Q R.νQ α :=
    PointGeometricCutState.ofOriginal ha
      (R.sides.straightening.trans Complex.conjCLE.toHomeomorph) R.ambient_halfplane
      R.νQ_representation.outside_eq R.νQ_representation.interior_eq hboundary
      (fun x hx ↦ R.budget_support_retained (Finsupp.mem_support_iff.mpr hx))
      R.budget_invariant (fun _ : Fin 1 ↦ E) hcover
  obtain ⟨s, _, hs, _, hbase, hmetric, _, _, hfront, _, hclean⟩ := R.clean_budget_ray
  let ρ : NNReal → ℂ := fun t ↦ top (s + (t:ℝ))
  have hρsupport : ρ 0 ∈ α.support := by
    apply Finsupp.mem_support_iff.mpr
    simpa only [ρ,top,NNReal.coe_zero,add_zero] using ne_of_gt hs
  let ray : K.CleanRay :=
    { ray := ρ, metric := hmetric, frontier := fun t ↦ hfront (mem_range_self t),
      clean := hclean, budget_supported := hρsupport }
  have he : ∀ x ∈ interior R.Q, R.νQ x = ν x := by
    intro x _
    rw [R.curvature_eq]
  exact ⟨{
    Q := R.Q
    curvature := R.νQ
    state := K
    clean := ray
    subset_old := R.subset_old
    curvature_mass := by rw [R.curvature_eq]
    negative_nonincrease := fun x ↦ by
      simpa only [R.curvature_eq] using (le_rfl : signedBudgetNeg (ν x) ≤ signedBudgetNeg (ν x))
    interior_unchanged := he
    rank_le := pointCutOuterRank_le_of_preparation_coefficients R.subset_old he }⟩

/-- Original current-region input suffices for the complete unmarked-frontier
branch, including its actual metric line, full strip, state, and clean ray. -/
theorem PointGeometricCutState.prepare_unmarked
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (hclean : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P)) :
    Nonempty (PointConstructedPreparation a y P ν α) := by
  let turn : ℂ → ℝ := fun x ↦ ν x
  have hturn : ∀ x ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P x,
      turn x = Real.pi - C.flatPhysicalWidth := by
    intro x hx
    obtain ⟨C, _, he⟩ := K.boundary_coeff x hx
    exact ⟨C, he⟩
  have hν : PointFullStripCurvatureRepresentation a y P turn ν :=
    ⟨K.interior_coeff, fun _ _ ↦ rfl, K.exterior_coeff⟩
  obtain ⟨line, _, _, _, _, _, _, R⟩ :=
    point_exists_actual_unmarked_boundary_preparation ha y K.ambient K.region_eq
      turn hturn ν α hν
      (fun x hx ↦ K.allocation_support x (Finsupp.mem_support_iff.mp hx)) K.budget hclean
  obtain ⟨R⟩ := R
  exact R.to_actual_preparation ha y

/-- A region already possessing a clean ray needs no strip at this stage. -/
def PointGeometricCutState.prepare_identity
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) (R : K.CleanRay) :
    PointConstructedPreparation a y P ν α :=
  { Q := P, curvature := ν, state := K, clean := R, subset_old := subset_rfl,
    curvature_mass := rfl, negative_nonincrease := fun _ ↦ le_rfl,
    interior_unchanged := fun _ _ ↦ rfl, rank_le := le_rfl }

/-- Honest preparation dichotomy. The unresolved alternative is exactly a
marked boundary with no actual clean budget ray, rather than a proposition
asserting that a decreasing preparation move somehow exists. -/
theorem PointGeometricCutState.preparation_or_marked_obstruction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α) :
    Nonempty (PointConstructedPreparation a y P ν α) ∨
      ((∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P) ∧ ¬Nonempty K.CleanRay) := by
  classical
  by_cases hR : Nonempty K.CleanRay
  · obtain ⟨R⟩ := hR
    exact Or.inl ⟨K.prepare_identity R⟩
  by_cases hmark : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P
  · exact Or.inr ⟨hmark, hR⟩
  · left
    exact K.prepare_unmarked ha y (Set.disjoint_left.mpr (fun x hx hf ↦ hmark ⟨x, hx, hf⟩))

end RepulsiveCoulomb
