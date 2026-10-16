module

public import LeanResearch.RepulsiveCoulomb.PointGeometricCutState

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual retained-apex next state and its strict
outer progress, plus the exact terminal branch. These constructions call the
actual geometric producers. No next-state or desired progress is a premise.
The disappearing-apex companion is selected separately after its source fix.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

namespace PointConstructedCutSector
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}

def apex (S : PointConstructedCutSector a y P ν α) : ℂ :=
  S.map (flatLinkSectorApex S.positive.le)

def top (S : PointConstructedCutSector a y P ν α) : NNReal → ℂ :=
  fun t ↦ S.map (retainedApexUpperSource S.positive.le S.le_pi t)

theorem apex_frontier (S : PointConstructedCutSector a y P ν α) : S.apex ∈ frontier P := by
  have he : retainedApexBottomSource S.positive.le S.le_pi 0 = flatLinkSectorApex S.positive.le :=
    Subtype.ext (sectorPolar_zero 0)
  simpa only [he,apex] using S.bottom_frontier 0

/-- Nonnegative residual mass is proved before testing the terminal branch. -/
theorem remaining_nonneg (K : PointGeometricCutState a y P ν α)
    (S : PointConstructedCutSector a y P ν α) :
    0 ≤ pointSignedBudgetMass ν α - S.beta :=
  sub_nonneg.mpr (S.le_budget.trans (pointCut_budgetCoeff_le_mass K.budget.budget_nonneg S.apex))

theorem terminal_exact_budget (K : PointGeometricCutState a y P ν α)
    (S : PointConstructedCutSector a y P ν α)
    (hzero : pointSignedBudgetMass ν α - S.beta = 0) :
    retainedApexBudget α S.apex S.beta = 0 ∧ α = Finsupp.single S.apex S.beta :=
  pointCut_terminal_spend K.budget.budget_nonneg S.le_budget hzero

/-- Exhaustive *scalar* endpoint alternatives; the full-angle alternative is
not discarded and does not inherit a positive residual-angle hypothesis. -/
theorem endpoint_cases (K : PointGeometricCutState a y P ν α)
    (S : PointConstructedCutSector a y P ν α) :
    pointSignedBudgetMass ν α - S.beta = 0 ∨
    (0 < pointSignedBudgetMass ν α - S.beta ∧ S.beta < S.chart.flatPhysicalWidth) ∨
    (0 < pointSignedBudgetMass ν α - S.beta ∧ S.chart.flatPhysicalWidth = S.beta) := by
  by_cases hz : pointSignedBudgetMass ν α - S.beta = 0
  · exact Or.inl hz
  have hp : 0 < pointSignedBudgetMass ν α - S.beta :=
    lt_of_le_of_ne (S.remaining_nonneg K) (Ne.symm hz)
  rcases lt_or_eq_of_le S.le_width with hw | hw
  · exact Or.inr (Or.inl ⟨hp, hw⟩)
  · exact Or.inr (Or.inr ⟨hp, hw.symm⟩)

end PointConstructedCutSector

/-- An actual output record. Unlike the current state, this records the cut
that has just been constructed, including its literal residual and proven
rank decrease. It has no fields asserting existence of future transitions. -/
structure PointConstructedSectorResidual {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (ν α : ℂ →₀ ℝ) (S : PointConstructedCutSector a y P ν α) where
  Q : Set ℂ
  curvature : ℂ →₀ ℝ
  state : PointGeometricCutState a y Q curvature (retainedApexBudget α S.apex S.beta)
  residual_eq : Q = closure (P \ range S.map)
  subset_old : Q ⊆ P
  interior_eq : interior Q = interior P \ range S.map
  curvature_mass : pointSignedCurvatureMass curvature (retainedApexBudget α S.apex S.beta) =
    pointSignedCurvatureMass ν α + S.beta
  budget_mass : pointSignedBudgetMass curvature (retainedApexBudget α S.apex S.beta) =
    pointSignedBudgetMass ν α - S.beta
  rank_lt : pointCutOuterRank Q curvature (retainedApexBudget α S.apex S.beta) <
    pointCutOuterRank P ν α

/-- Actual current-state interpretations imply equality of both coefficients
on the new interior; no support/rank certificate is taken as an input. -/
theorem pointCut_interior_coefficients_after_spend
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ} {ν α μ : ℂ →₀ ℝ}
    (K : PointGeometricCutState a y P ν α) (S : PointConstructedCutSector a y P ν α)
    (L : PointGeometricCutState a y Q μ (retainedApexBudget α S.apex S.beta)) (hQP : Q ⊆ P) :
    (∀ x ∈ interior Q, μ x = ν x) ∧
    (∀ x ∈ interior Q, retainedApexBudget α S.apex S.beta x = α x) := by
  constructor
  · intro x hx
    exact (L.interior_coeff x hx).trans (K.interior_coeff x (interior_mono hQP hx)).symm
  · intro x hx
    exact retainedApexBudget_off α S.beta (fun he ↦ S.apex_frontier.2 (he ▸ interior_mono hQP hx))

/-- The actual exposed mark, not its cardinality consequence, supplies the
third alternative when neither scalar cap is reached. -/
theorem pointConstructedSector_cap_or_actual_exposure
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ} {ν α : ℂ →₀ ℝ}
    (S : PointConstructedCutSector a y P ν α)
    (hi : ∀ t : NNReal, 0 < (t:ℝ) → S.top t ∈ interior P)
    (hf : range S.top ⊆ frontier Q) :
    S.beta = Real.pi ∨ S.beta = α S.apex ∨
      ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ interior P ∧ x ∈ frontier Q := by
  by_cases hp : S.beta = Real.pi
  · exact Or.inl hp
  by_cases hα : S.beta = α S.apex
  · exact Or.inr (Or.inl hα)
  have hc : S.beta < min Real.pi (α S.apex) :=
    lt_min (lt_of_le_of_ne S.le_pi hp) (lt_of_le_of_ne S.le_budget hα)
  obtain ⟨t, ht, hm⟩ := S.first_top hc
  exact Or.inr (Or.inr ⟨S.top t, hm, hi t ht, hf (mem_range_self t)⟩)

/-- Genuine retained-apex next state, with all original invariants and actual
discrete rank decrease derived from the constructed sector. -/
theorem PointConstructedCutSector.retained_step
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (S : PointConstructedCutSector a y P ν α)
    (hremaining : 0 < pointSignedBudgetMass ν α - S.beta)
    (hwidth : S.beta < S.chart.flatPhysicalWidth) :
    Nonempty (PointConstructedSectorResidual a y P ν α S) := by
  obtain ⟨O⟩ := point_actual_retained_apex_iteration_output ha y S.positive S.le_pi
    S.map S.metric K.ambient K.region_eq S.mem_region S.bottom_frontier
    K.pieces K.boundary_cover S.chart S.admissible hwidth ν α K.budget S.le_budget hremaining
    K.exterior_coeff K.interior_coeff
    (fun x hx ↦ by obtain ⟨C, hC, he⟩ := K.boundary_coeff x hx; exact ⟨C, he, hC⟩)
    K.allocation_support S.clean_bottom S.clean_open
  let Q := closure (P \ range S.map)
  let μ := retainedApexCurvature ν S.apex S.beta
  let L : PointGeometricCutState a y Q μ (retainedApexBudget α S.apex S.beta) :=
    { ambient := O.ambient, region_eq := O.region_eq, connected := O.connected,
      charts := O.charts, interior_coeff := O.interior_coeff,
      boundary_coeff := fun x hx ↦ by
        obtain ⟨C, he, hC⟩ := O.boundary_coeff x hx
        exact ⟨C, hC, he⟩,
      exterior_coeff := O.exterior_coeff, allocation_support := O.allocation_support,
      budget := O.budget_invariant, pieceCount := K.pieceCount + 1,
      pieces := O.boundary_pieces, boundary_cover := O.boundary_cover }
  obtain ⟨hν, hα⟩ := pointCut_interior_coefficients_after_spend K S L O.subset_old
  have hevent := pointConstructedSector_cap_or_actual_exposure S O.open_top_old_interior O.top_frontier
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

theorem PointConstructedSectorResidual.disjoint_old_sector_new_interior
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    {S : PointConstructedCutSector a y P ν α} (O : PointConstructedSectorResidual a y P ν α S) :
    Disjoint (range S.map) (interior O.Q) := by
  rw [O.interior_eq]
  exact Set.disjoint_left.mpr (fun _ hx hy ↦ hy.2 hx)

end RepulsiveCoulomb
