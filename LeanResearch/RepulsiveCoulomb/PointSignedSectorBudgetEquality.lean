module

public import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudget
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Tactic.Ext

@[expose] public section

/-!
Full-angle rigidity in Pro Lemma 5.1. The premises are only the original budget
invariant, the boundary coefficient identity, and the two scalar caps on beta.
The conclusions used in the disappearing-apex sector cut are proved, not stored
in a certificate. No sector, cut, or residual-region existence is claimed.
-/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb
namespace PointSignedBudgetInvariant

variable {ν α : ℂ →₀ ℝ} (h : PointSignedBudgetInvariant ν α)
include h

/-- Equality at the full boundary angle forces all four conclusions of (5.5).
The split hypotheses beta ≤ pi and beta ≤ alpha(y) are exactly beta ≤ min(...).
This algebraic strengthening does not require y to be in supp(alpha). -/
theorem full_angle_equality (y : ℂ) {β : ℝ}
    (hboundary : ν y = Real.pi - β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α y) :
    α y = β ∧ ν y = Real.pi - β ∧ 0 ≤ ν y ∧
      pointSignedPositiveMassAway ν α y = 0 ∧
      (∀ x, x ≠ y → α x = signedBudgetNeg (ν x)) := by
  have hν : 0 ≤ ν y := by linarith
  have hαβ : α y = β :=
    le_antisymm (h.budget_le_boundary_angle_of_nonneg y hboundary hν) hβα
  have hpos : signedBudgetPos (ν y) = ν y := max_eq_left hν
  have hneg : signedBudgetNeg (ν y) = 0 := max_eq_right (neg_nonpos.mpr hν)
  have hE : β ≤ pointSignedSurplusMass ν α := by
    have hc := h.surplusCoeff_le_mass y
    simpa [hαβ, hneg] using hc
  have hP : Real.pi - β ≤ pointSignedPositiveMass ν α := by
    calc
      Real.pi - β = ν y := hboundary.symm
      _ = signedBudgetPos (ν y) := hpos.symm
      _ ≤ pointSignedPositiveMass ν α := h.positiveCoeff_le_mass y
  have hEP := h.surplusMass_add_positiveMass_le_pi
  have hEe : pointSignedSurplusMass ν α = β := by linarith
  have hPe : pointSignedPositiveMass ν α = Real.pi - β := by linarith
  have hPaway : pointSignedPositiveMassAway ν α y = 0 := by
    have hs := pointSignedPositiveMassAway_add ν α y
    rw [hpos, hboundary, hPe] at hs
    linarith
  have hEaway : pointSignedSurplusMassAway ν α y = 0 := by
    have hs := pointSignedSurplusMassAway_add ν α y
    rw [hαβ, hneg, hEe] at hs
    linarith
  exact ⟨hαβ, hboundary, hν, hPaway,
    h.budget_eq_negative_off_of_surplusMassAway_eq_zero y hEaway⟩

/-- The form appearing literally in Pro: lambda_P(y)=beta ≤ min(pi,alpha(y)). -/
theorem full_angle_equality_of_min (y : ℂ) {linkAngle β : ℝ}
    (hboundary : ν y = Real.pi - linkAngle) (hfull : linkAngle = β)
    (hcap : β ≤ min Real.pi (α y)) :
    α y = β ∧ ν y = Real.pi - β ∧ 0 ≤ ν y ∧
      pointSignedPositiveMassAway ν α y = 0 ∧
      (∀ x, x ≠ y → α x = signedBudgetNeg (ν x)) := by
  apply h.full_angle_equality y
  · simpa [hfull] using hboundary
  · exact (le_min_iff.mp hcap).1
  · exact (le_min_iff.mp hcap).2

/-- Rigidity expressed as an equality of ambient finitely supported functions:
all budget surplus is the beta atom at the disappearing apex. -/
theorem full_angle_surplus_single (y : ℂ) {β : ℝ}
    (hboundary : ν y = Real.pi - β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α y) :
    α = pointSignedNegativePart ν + Finsupp.single y β := by
  classical
  obtain ⟨hαβ, hνβ, hν, haway, hoff⟩ := h.full_angle_equality y hboundary hβπ hβα
  have hneg : signedBudgetNeg (ν y) = 0 := max_eq_right (neg_nonpos.mpr hν)
  ext x
  simp only [Finsupp.add_apply, pointSignedNegativePart_apply]
  by_cases hxy : x = y
  · subst x
    simp [hαβ, hneg]
  · simp [hoff x hxy, hxy, Ne.symm hxy]

/-- In particular there is no other positive-turn atom; the off-y equality is
also retained in coefficient form for support-retention arguments. -/
theorem full_angle_off_apex_nonpositive (y : ℂ) {β : ℝ}
    (hboundary : ν y = Real.pi - β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α y) :
    ∀ x, x ≠ y → ν x ≤ 0 := by
  classical
  obtain ⟨hαβ, hνβ, hν, haway, hoff⟩ := h.full_angle_equality y hboundary hβπ hβα
  intro x hxy
  by_cases hx : x ∈ pointSignedMarked ν α
  · have hx' : x ∈ (pointSignedMarked ν α).erase y :=
      Finset.mem_erase.mpr ⟨hxy, hx⟩
    have hsingle : signedBudgetPos (ν x) ≤ pointSignedPositiveMassAway ν α y :=
      Finset.single_le_sum (fun z hz => signedBudgetPos_nonneg (ν z)) hx'
    have hle : ν x ≤ signedBudgetPos (ν x) := le_max_left _ _
    linarith
  · exact le_of_eq (pointSigned_eq_zero_off_marked hx).1

end PointSignedBudgetInvariant
end RepulsiveCoulomb
