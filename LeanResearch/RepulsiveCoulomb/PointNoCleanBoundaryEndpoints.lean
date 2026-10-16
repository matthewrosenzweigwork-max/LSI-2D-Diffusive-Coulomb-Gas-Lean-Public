module

public import LeanResearch.RepulsiveCoulomb.PointSaturatedTwoCornerBudget
public import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryRayContacts
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. Original no-clean-budget-ray hypotheses are expressed
literally in terms of actual ambient metric boundary rays. They imply positive
turn at a clean marked endpoint. A finite boundary clock also produces an
actual last marked point. Converting its unmarked topological tail into a
minimizing arclength ray remains a geometric construction, not a field here.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The literal original obstruction, quantified over actual rays. This is
equivalent to nonexistence of the clean budget ray in the geometric cut state;
it does not assert any future strip, last point, or residual geometry. -/
def PointNoCleanBudgetBoundaryRay {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (ν α : ℂ →₀ ℝ) : Prop :=
  ¬ ∃ ρ : NNReal → ℂ,
    (∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t) ∧
    (∀ t, ρ t ∈ frontier P) ∧
    Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ) ∧
    α (ρ 0) ≠ 0

/-- Once the actual outward boundary ray has been constructed at a marked
endpoint, no-clean-budget gives zero allocation and forces its old turn to be
strictly positive. There is no positive-turn premise. -/
theorem pointNoCleanBudgetBoundaryRay_marked_endpoint
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (hbudget : PointSignedBudgetInvariant ν α)
    (hno : PointNoCleanBudgetBoundaryRay a y P ν α)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hfront : ∀ t, ρ t ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hmarked : ρ 0 ∈ pointSignedMarked ν α) :
    α (ρ 0) = 0 ∧ 0 < ν (ρ 0) := by
  have hzero : α (ρ 0) = 0 := by
    by_contra hn
    exact hno ⟨ρ, hρ, hfront, hclean, hn⟩
  exact ⟨hzero, pointSigned_marked_zero_budget_positive hbudget hmarked hzero⟩

/-- Saturation identifies the opposite outermost point with the attained
corner once its genuine clean outward ray is available. This is a direct
application of the original no-clean obstruction, not an assumed equality. -/
theorem pointNoCleanBudgetBoundaryRay_saturated_endpoint_eq
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (hbudget : PointSignedBudgetInvariant ν α)
    (hno : PointNoCleanBudgetBoundaryRay a y P ν α)
    {p z : ℂ} (hpz : p ≠ z) (hp : 0 < ν p) (hz : 0 < ν z)
    (hsum : ν p + ν z = Real.pi)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hfront : ∀ t, ρ t ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hmarked : ρ 0 ∈ pointSignedMarked ν α) (hother : ρ 0 ≠ p) :
    ρ 0 = z := by
  have hzero := (pointNoCleanBudgetBoundaryRay_marked_endpoint
    hbudget hno ρ hρ hfront hclean hmarked).1
  exact pointSigned_saturated_last_mark_eq_target
    hbudget hpz hp hz hsum hother hmarked hzero

/-- Finite marks have an actual last boundary clock value. Clock injectivity
is not needed to pick it; it is only needed later to identify a tail endpoint.
No metric property of the topological boundary parameterization is inferred. -/
theorem pointSigned_exists_last_boundary_mark
    {ν α : ℂ →₀ ℝ} {P : Set ℂ} (clock : ℂ → ℝ)
    (hne : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P) :
    ∃ w, w ∈ pointSignedMarked ν α ∧ w ∈ frontier P ∧
      ∀ x, x ∈ pointSignedMarked ν α → x ∈ frontier P → clock x ≤ clock w := by
  classical
  let S := (pointSignedMarked ν α).filter (fun x ↦ x ∈ frontier P)
  have hS : S.Nonempty := by
    obtain ⟨x, hx, hfront⟩ := hne
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hfront⟩⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image S clock hS
  obtain ⟨hwm, hwfront⟩ := Finset.mem_filter.mp hw
  exact ⟨w, hwm, hwfront, fun x hx hfront ↦
    hmax x (Finset.mem_filter.mpr ⟨hx, hfront⟩)⟩

end RepulsiveCoulomb
