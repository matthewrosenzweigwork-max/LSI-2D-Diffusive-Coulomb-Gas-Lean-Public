import LeanResearch.RepulsiveCoulomb.PointSignedCurvatureFinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The actual scalar hypotheses of Pro Lemma 5.1: domination of the negative part,
positive allocation mass, and A + V ≤ pi. Every bound below is derived.
There is no geometric region certificate and no assumed target inequality.
-/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Pro equation (5.1), expressed for finite coefficients on ambient C.
Nonnegativity of alpha follows from domination and is not a redundant field. -/
structure PointSignedBudgetInvariant (ν α : ℂ →₀ ℝ) : Prop where
  dominates : ∀ x, signedBudgetNeg (ν x) ≤ α x
  budget_pos : 0 < pointSignedBudgetMass ν α
  mass_le : pointSignedBudgetMass ν α + pointSignedCurvatureMass ν α ≤ Real.pi

/-- Exact equivalence with the original A <= pi - V presentation. -/
theorem pointSignedBudgetInvariant_iff (ν α : ℂ →₀ ℝ) :
    PointSignedBudgetInvariant ν α ↔
      (∀ x, signedBudgetNeg (ν x) ≤ α x) ∧
      0 < pointSignedBudgetMass ν α ∧
      pointSignedBudgetMass ν α ≤ Real.pi - pointSignedCurvatureMass ν α := by
  constructor
  · intro h
    refine ⟨h.dominates, h.budget_pos, ?_⟩
    have hm := h.mass_le
    linarith
  · rintro ⟨hd, hp, hm⟩
    exact ⟨hd, hp, by linarith⟩

namespace PointSignedBudgetInvariant

variable {ν α : ℂ →₀ ℝ} (h : PointSignedBudgetInvariant ν α)
include h

theorem budget_nonneg (x : ℂ) : 0 ≤ α x :=
  (signedBudgetNeg_nonneg (ν x)).trans (h.dominates x)

theorem surplus_nonneg (x : ℂ) : 0 ≤ α x - signedBudgetNeg (ν x) :=
  sub_nonneg.mpr (h.dominates x)

theorem positiveMass_nonneg : 0 ≤ pointSignedPositiveMass ν α :=
  Finset.sum_nonneg (fun x hx => signedBudgetPos_nonneg (ν x))

theorem negativeMass_nonneg : 0 ≤ pointSignedNegativeMass ν α :=
  Finset.sum_nonneg (fun x hx => signedBudgetNeg_nonneg (ν x))

theorem surplusMass_nonneg : 0 ≤ pointSignedSurplusMass ν α :=
  Finset.sum_nonneg (fun x hx => h.surplus_nonneg x)

theorem negativeMass_le_budgetMass :
    pointSignedNegativeMass ν α ≤ pointSignedBudgetMass ν α :=
  Finset.sum_le_sum (fun x hx => h.dominates x)

/-- V < pi uses the genuinely positive residual allocation. -/
theorem curvatureMass_lt_pi : pointSignedCurvatureMass ν α < Real.pi := by
  have hA := h.budget_pos
  have hAV := h.mass_le
  linarith

/-- Total positive curvature-and-boundary-turn mass is at most pi. -/
theorem positiveMass_le_pi : pointSignedPositiveMass ν α ≤ Real.pi := by
  have hdecomp := pointSignedPositiveMass_sub_negativeMass ν α
  have hdom := h.negativeMass_le_budgetMass
  have hAV := h.mass_le
  linarith

/-- The slack is a nonnegative finite coefficient function with mass E. -/
theorem surplusMass_add_positiveMass_le_pi :
    pointSignedSurplusMass ν α + pointSignedPositiveMass ν α ≤ Real.pi := by
  have hdecomp := pointSignedPositiveMass_sub_negativeMass ν α
  have hsurplus := pointSignedSurplusMass_eq_budget_sub_negative ν α
  have hAV := h.mass_le
  linarith

theorem positiveCoeff_le_mass (y : ℂ) :
    signedBudgetPos (ν y) ≤ pointSignedPositiveMass ν α := by
  classical
  by_cases hy : y ∈ pointSignedMarked ν α
  · exact Finset.single_le_sum (fun x hx => signedBudgetPos_nonneg (ν x)) hy
  · have hν := (pointSigned_eq_zero_off_marked hy).1
    simpa [hν] using h.positiveMass_nonneg

theorem surplusCoeff_le_mass (y : ℂ) :
    α y - signedBudgetNeg (ν y) ≤ pointSignedSurplusMass ν α := by
  classical
  by_cases hy : y ∈ pointSignedMarked ν α
  · exact Finset.single_le_sum (fun x hx => h.surplus_nonneg x) hy
  · obtain ⟨hν, hα⟩ := pointSigned_eq_zero_off_marked hy
    simpa [hν, hα] using h.surplusMass_nonneg

theorem positiveMassAway_nonneg (y : ℂ) :
    0 ≤ pointSignedPositiveMassAway ν α y := by
  classical
  exact Finset.sum_nonneg (fun x hx => signedBudgetPos_nonneg (ν x))

theorem surplusMassAway_nonneg (y : ℂ) :
    0 ≤ pointSignedSurplusMassAway ν α y := by
  classical
  exact Finset.sum_nonneg (fun x hx => h.surplus_nonneg x)

/-- Pro (5.3). The proof even holds when the ambient apex is not marked. -/
theorem positive_part_cap (y : ℂ) {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ : θ ≤ α y) :
    pointSignedPositiveMassAway ν α y + signedBudgetPos (ν y + θ) ≤ Real.pi := by
  have hincrement := signedBudgetPos_increment_le (h.dominates y) hθ
  have hcoeff := h.surplusCoeff_le_mass y
  have hsplit := pointSignedPositiveMassAway_add ν α y
  have htotal := h.surplusMass_add_positiveMass_le_pi
  linarith

/-- The nonnegative-turn case of the boundary estimate, used also by rigidity. -/
theorem budget_le_boundary_angle_of_nonneg (y : ℂ) {linkAngle : ℝ}
    (hboundary : ν y = Real.pi - linkAngle) (hν : 0 ≤ ν y) : α y ≤ linkAngle := by
  have hpos : signedBudgetPos (ν y) = ν y := max_eq_left hν
  have hneg : signedBudgetNeg (ν y) = 0 := max_eq_right (neg_nonpos.mpr hν)
  have hcoeff := h.surplusCoeff_le_mass y
  have hpositive := h.positiveCoeff_le_mass y
  have htotal := h.surplusMass_add_positiveMass_le_pi
  rw [hneg] at hcoeff
  rw [hpos] at hpositive
  linarith

/-- Pro (5.4), with the actual boundary atom formula supplied explicitly.
No link-angle lower bound or budget cap is assumed. -/
theorem min_pi_budget_le_boundary_angle (y : ℂ) {linkAngle : ℝ}
    (hboundary : ν y = Real.pi - linkAngle) : min Real.pi (α y) ≤ linkAngle := by
  by_cases hν : 0 ≤ ν y
  · exact (min_le_right _ _).trans (h.budget_le_boundary_angle_of_nonneg y hboundary hν)
  · have hlinkAngle : Real.pi ≤ linkAngle := by linarith
    exact (min_le_left _ _).trans hlinkAngle

/-- A finite nonnegative slack sum vanishing away from y forces every
individual off-y slack to vanish, including points outside the marked set. -/
theorem budget_eq_negative_off_of_surplusMassAway_eq_zero (y : ℂ)
    (hzero : pointSignedSurplusMassAway ν α y = 0) :
    ∀ x, x ≠ y → α x = signedBudgetNeg (ν x) := by
  classical
  intro x hxy
  by_cases hx : x ∈ pointSignedMarked ν α
  · have hx' : x ∈ (pointSignedMarked ν α).erase y :=
      Finset.mem_erase.mpr ⟨hxy, hx⟩
    have hsingle : α x - signedBudgetNeg (ν x) ≤ pointSignedSurplusMassAway ν α y :=
      Finset.single_le_sum (fun z hz => h.surplus_nonneg z) hx'
    have hnonneg := h.surplus_nonneg x
    linarith
  · obtain ⟨hν, hα⟩ := pointSigned_eq_zero_off_marked hx
    simp [hν, hα]

end PointSignedBudgetInvariant
end RepulsiveCoulomb
