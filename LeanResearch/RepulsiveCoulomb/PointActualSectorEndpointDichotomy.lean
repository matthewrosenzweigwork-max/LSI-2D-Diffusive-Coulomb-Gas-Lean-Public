import LeanResearch.RepulsiveCoulomb.PointConstructedSectorProgress
import LeanResearch.RepulsiveCoulomb.PointActualDisappearingApexIteration

/-! SOURCE-ONLY, UNCOMPILED. Uses the uniquely selected Classical-cover Case II
successor, never its known-broken predecessor. Both nonterminal endpoint
branches produce genuine current states and strict discrete rank decrease.
The terminal branch stops with the actual sector and exact remaining budget;
it neither constructs a residual region nor asserts sector coverage of P.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem PointConstructedCutSector.disappearing_step
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (S : PointConstructedCutSector a y P ν α)
    (hremaining : 0 < pointSignedBudgetMass ν α - S.beta)
    (hwidth : S.chart.flatPhysicalWidth = S.beta) :
    Nonempty (PointConstructedSectorResidual a y P ν α S) := by
  obtain ⟨r, hr, _, _, O⟩ := point_actual_disappearing_apex_sector_iteration ha y
    S.positive S.le_pi S.map S.metric K.ambient K.region_eq S.mem_region S.bottom_frontier
    K.pieces K.boundary_cover S.chart S.admissible hwidth ν α K.budget S.le_budget hremaining
    K.exterior_coeff K.interior_coeff
    (fun x hx ↦ by obtain ⟨C, hC, he⟩ := K.boundary_coeff x hx; exact ⟨C, he, hC⟩)
    K.allocation_support S.clean_bottom S.clean_open
  obtain ⟨O⟩ := O
  obtain ⟨pieces, hpieces⟩ := O.finite_boundary_cover
  let Q := closure (P \ range S.map)
  let τ : NNReal → ℂ := fun t ↦ S.map (disappearingSectorTail S.positive.le S.le_pi r t)
  let μ := disappearingApexCurvature ν S.apex (τ 0)
  let L : PointGeometricCutState a y Q μ (retainedApexBudget α S.apex S.beta) :=
    { toPointRetainedSignedHalfplaneState := O.state,
      budget := O.budget_invariant, pieceCount := K.pieceCount + 1,
      pieces := pieces, boundary_cover := hpieces }
  obtain ⟨hν, hα⟩ := pointCut_interior_coefficients_after_spend K S L O.subset_old
  have hevent : S.beta = Real.pi ∨ S.beta = α S.apex ∨
      ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ interior P ∧ x ∈ frontier Q :=
    Or.inr (Or.inl O.apex_budget_spent.symm)
  have hrank := pointCutOuterRank_lt_of_event S.positive S.le_budget hremaining
    O.allocation_mass O.subset_old hν hα hevent
  exact ⟨{
    Q := Q
    curvature := μ
    state := L
    residual_eq := rfl
    subset_old := O.subset_old
    interior_eq := O.interior_eq
    curvature_mass := O.curvature_mass
    budget_mass := O.allocation_mass
    rank_lt := hrank }⟩

/-- Complete actual sector endpoint alternatives. All transitions come from
actual producers, and no move-existence or rank premise appears. -/
theorem PointConstructedCutSector.terminal_or_actual_residual
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (S : PointConstructedCutSector a y P ν α) :
    (retainedApexBudget α S.apex S.beta = 0 ∧ α = Finsupp.single S.apex S.beta) ∨
      Nonempty (PointConstructedSectorResidual a y P ν α S) := by
  rcases S.endpoint_cases K with hz | ⟨hpos, hretained⟩ | ⟨hpos, hfull⟩
  · exact Or.inl (S.terminal_exact_budget K hz)
  · exact Or.inr (S.retained_step ha y K hpos hretained)
  · exact Or.inr (S.disappearing_step ha y K hpos hfull)

/-- Starting with an actual prepared current region, the positive sector and
both geometric endpoint branches are now assembled. Preparation for the next
region is not assumed here, so this is not mislabelled a finite allocation. -/
theorem PointGeometricCutState.construct_sector_and_step
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (R : K.CleanRay) :
    ∃ S : PointConstructedCutSector a y P ν α,
      (retainedApexBudget α S.apex S.beta = 0 ∧ α = Finsupp.single S.apex S.beta) ∨
        Nonempty (PointConstructedSectorResidual a y P ν α S) := by
  obtain ⟨S⟩ := K.construct_sector ha y R
  exact ⟨S, S.terminal_or_actual_residual ha y K⟩

end RepulsiveCoulomb
