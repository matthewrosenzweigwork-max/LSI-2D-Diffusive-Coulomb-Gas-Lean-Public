module

public import LeanResearch.RepulsiveCoulomb.PointFullStripCurvatureTransport
public import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudget
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual ambient Finsupp representation and finite
support adapters for the full-line preparation. The old representation records
its genuine interior, boundary and off-region meanings. None of the residual,
contact, support-preservation or rank conclusions is an input to the geometric
constructor which consumes these adapters. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- Old-state interpretation, separately from the genuine boundary charts.
The function `turn` is used only on the old frontier. -/
structure PointFullStripCurvatureRepresentation {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (P : Set ℂ)
    (turn : ℂ → ℝ) (ν : ℂ →₀ ℝ) : Prop where
  interior_eq : ∀ p ∈ interior P, ν p = -Real.pi * coalescedPointExponent a y p
  boundary_eq : ∀ p ∈ frontier P, ν p = turn p
  outside_eq : ∀ p ∉ P, ν p = 0

namespace PointFullStripCurvatureRepresentation
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ}
  {turn : ℂ → ℝ} {ν α : ℂ →₀ ℝ}

/-- The composite geometric coefficient really is the given arbitrary ν. -/
theorem coefficient_eq (h : PointFullStripCurvatureRepresentation a y P turn ν)
    (hP : IsClosed P) (p : ℂ) :
    pointFullStripSignedCoefficient a y P turn p = ν p := by
  by_cases hi : p ∈ interior P
  · simpa only [pointFullStripSignedCoefficient, if_pos hi] using (h.interior_eq p hi).symm
  by_cases hf : p ∈ frontier P
  · simpa only [pointFullStripSignedCoefficient, if_neg hi, if_pos hf] using
      (h.boundary_eq p hf).symm
  have hp : p ∉ P := fun hp ↦ hf ⟨hP.closure_eq.symm ▸ hp, hi⟩
  simpa only [pointFullStripSignedCoefficient, if_neg hi, if_neg hf] using
    (h.outside_eq p hp).symm

/-- Conversely, the all-point composite identity recovers all three actual
geometric clauses, rather than merely a name for the coefficient function. -/
theorem of_coefficient_eq (hP : IsClosed P)
    (hc : ∀ p, ν p = pointFullStripSignedCoefficient a y P turn p) :
    PointFullStripCurvatureRepresentation a y P turn ν := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simpa only [pointFullStripSignedCoefficient, if_pos hp] using hc p
  · intro p hp
    simpa only [pointFullStripSignedCoefficient, if_neg hp.2, if_pos hp] using hc p
  · intro p hp
    have hi : p ∉ interior P := fun hi ↦ hp (interior_subset hi)
    have hf : p ∉ frontier P := fun hf ↦ hp (hP.frontier_subset hf)
    simpa only [pointFullStripSignedCoefficient, if_neg hi, if_neg hf] using hc p

theorem support_subset (h : PointFullStripCurvatureRepresentation a y P turn ν) :
    (↑ν.support : Set ℂ) ⊆ P := by
  intro p hp
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hp) (h.outside_eq p hn)

theorem interior_marked (h : PointFullStripCurvatureRepresentation a y P turn ν)
    (α : ℂ →₀ ℝ) :
    ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 →
      p ∈ (↑(pointSignedMarked ν α) : Set ℂ) := by
  intro p hp hn
  apply (mem_pointSignedMarked ν α p).mpr
  left
  rw [h.interior_eq p hp]
  exact mul_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero) hn

theorem boundary_marked (h : PointFullStripCurvatureRepresentation a y P turn ν)
    (α : ℂ →₀ ℝ) :
    ∀ p ∈ frontier P, turn p ≠ 0 →
      p ∈ (↑(pointSignedMarked ν α) : Set ℂ) := by
  intro p hp hn
  exact (mem_pointSignedMarked ν α p).mpr (Or.inl (by rwa [h.boundary_eq p hp]))

/-- On old-interior marks, domination makes the actual budget strictly
positive, whether the mark is curvature-supported or budget-only. -/
theorem marked_interior_budget_pos
    (h : PointFullStripCurvatureRepresentation a y P turn ν)
    (hdom : ∀ p, signedBudgetNeg (ν p) ≤ α p)
    {p : ℂ} (hp : p ∈ interior P) (hm : p ∈ pointSignedMarked ν α) :
    0 < α p := by
  have hα : 0 ≤ α p := (signedBudgetNeg_nonneg (ν p)).trans (hdom p)
  rcases (mem_pointSignedMarked ν α p).mp hm with hν | hαne
  · have hnonpos : ν p ≤ 0 := by
      rw [h.interior_eq p hp]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le)
        (coalescedPointExponent_nonneg a y p)
    have hneg : ν p < 0 := lt_of_le_of_ne hnonpos hν
    have hnegpart : 0 < signedBudgetNeg (ν p) :=
      (neg_pos.mpr hneg).trans_le (le_max_left _ _)
    exact hnegpart.trans_le (hdom p)
  · exact lt_of_le_of_ne hα (Ne.symm hαne)
end PointFullStripCurvatureRepresentation

/-- Positive budget mass forces the actual union of both supports nonempty. -/
theorem pointFullLine_actual_marks_nonempty {ν α : ℂ →₀ ℝ}
    (hA : 0 < pointSignedBudgetMass ν α) :
    (↑(pointSignedMarked ν α) : Set ℂ).Nonempty := by
  classical
  have hn : (pointSignedMarked ν α).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : pointSignedBudgetMass ν α = 0 := by
      simp only [pointSignedBudgetMass, he, Finset.sum_empty]
    exact (ne_of_gt hA) hz
  exact hn

theorem pointFullLine_budget_subset_actual_marks (ν α : ℂ →₀ ℝ) :
    (↑α.support : Set ℂ) ⊆ (↑(pointSignedMarked ν α) : Set ℂ) := by
  intro p hp
  exact (mem_pointSignedMarked ν α p).mpr (Or.inr (Finsupp.mem_support_iff.mp hp))

/-- Build a finite coefficient object from a derived all-point identity.
This uses the old finite support only as a bounding finset; onFinset computes
its actual support by filtering the new coefficient's nonzero values. -/
def pointFullStripFinsuppOfCoefficient (ν : ℂ →₀ ℝ) (c : ℂ → ℝ)
    (hc : ∀ p, c p = ν p) : ℂ →₀ ℝ :=
  Finsupp.onFinset ν.support c (fun p hp ↦ Finsupp.mem_support_iff.mpr (by
    rw [← hc p]
    exact hp))

@[simp] theorem pointFullStripFinsuppOfCoefficient_apply (ν : ℂ →₀ ℝ)
    (c : ℂ → ℝ) (hc : ∀ p, c p = ν p) (p : ℂ) :
    pointFullStripFinsuppOfCoefficient ν c hc p = c p := rfl

theorem pointFullStripFinsuppOfCoefficient_eq (ν : ℂ →₀ ℝ)
    (c : ℂ → ℝ) (hc : ∀ p, c p = ν p) :
    pointFullStripFinsuppOfCoefficient ν c hc = ν := by
  ext p
  exact hc p

/-- Any other ambient Finsupp with the actual new geometric interpretation
is equal too; the result is not restricted to the chosen finite constructor. -/
theorem pointFullStrip_finsupp_eq_of_coefficients {ν νQ : ℂ →₀ ℝ}
    {c : ℂ → ℝ} (hQ : ∀ p, νQ p = c p) (hc : ∀ p, c p = ν p) : νQ = ν := by
  ext p
  exact (hQ p).trans (hc p)

/-- Literal support/filter comparisons. The finite expression on the final
line is n+i, and agrees definitionally with the isolated rank draft's rank. -/
theorem pointFullStrip_support_and_interior_counts {ν νQ : ℂ →₀ ℝ}
    {P Q : Set ℂ} (hν : νQ = ν) (hQP : Q ⊆ P) :
    νQ.support = ν.support ∧ νQ.support.card = ν.support.card ∧
    (νQ.support.filter (fun p ↦ p ∈ interior Q)) ⊆
      (ν.support.filter (fun p ↦ p ∈ interior P)) ∧
    (νQ.support.filter (fun p ↦ p ∈ interior Q)).card ≤
      (ν.support.filter (fun p ↦ p ∈ interior P)).card ∧
    νQ.support.card + (νQ.support.filter (fun p ↦ p ∈ interior Q)).card ≤
      ν.support.card + (ν.support.filter (fun p ↦ p ∈ interior P)).card := by
  classical
  subst νQ
  have hs : (ν.support.filter (fun p ↦ p ∈ interior Q)) ⊆
      (ν.support.filter (fun p ↦ p ∈ interior P)) := by
    intro p hp
    obtain ⟨hνp, hpQ⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hνp, interior_mono hQP hpQ⟩
  have hn := Finset.card_le_card hs
  exact ⟨rfl, rfl, hs, hn, Nat.add_le_add_left hn _⟩

end RepulsiveCoulomb
