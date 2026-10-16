import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
Finite signed curvature coefficients on the fixed ambient complex plane.
The finite marked set is the actual union of the two Finsupp supports. Positive
and negative parts are coefficients, with no ambient nonpositivity assumption.
This file contains only finite algebra, not construction of a geometric region.
-/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The positive coefficient of a signed real atom. -/
def signedBudgetPos (r : ℝ) : ℝ := max r 0

/-- The magnitude of the negative coefficient of a signed real atom. -/
def signedBudgetNeg (r : ℝ) : ℝ := max (-r) 0

@[simp] theorem signedBudgetPos_zero : signedBudgetPos 0 = 0 := by
  simp [signedBudgetPos]

@[simp] theorem signedBudgetNeg_zero : signedBudgetNeg 0 = 0 := by
  simp [signedBudgetNeg]

theorem signedBudgetPos_nonneg (r : ℝ) : 0 ≤ signedBudgetPos r :=
  le_max_right _ _

theorem signedBudgetNeg_nonneg (r : ℝ) : 0 ≤ signedBudgetNeg r :=
  le_max_right _ _

theorem signedBudgetPos_sub_neg (r : ℝ) :
    signedBudgetPos r - signedBudgetNeg r = r := by
  rcases le_total 0 r with hr | hr
  · simp [signedBudgetPos, signedBudgetNeg, max_eq_left hr,
      max_eq_right (neg_nonpos.mpr hr)]
  · simp [signedBudgetPos, signedBudgetNeg, max_eq_right hr,
      max_eq_left (neg_nonneg.mpr hr)]

/-- Exact scalar increment estimate; nonnegative theta is unnecessary here. -/
theorem signedBudgetPos_increment_le {r a θ : ℝ}
    (ha : signedBudgetNeg r ≤ a) (hθ : θ ≤ a) :
    signedBudgetPos (r + θ) - signedBudgetPos r ≤ a - signedBudgetNeg r := by
  have hn : -r ≤ signedBudgetNeg r := le_max_left _ _
  have hupper : signedBudgetPos (r + θ) ≤ r + a := by
    apply max_le
    · linarith
    · linarith
  have hid := signedBudgetPos_sub_neg r
  linarith

/-- Actual finitely supported positive part on ambient C. -/
def pointSignedPositivePart (ν : ℂ →₀ ℝ) : ℂ →₀ ℝ :=
  Finsupp.mapRange signedBudgetPos signedBudgetPos_zero ν

/-- Actual finitely supported negative part on ambient C. -/
def pointSignedNegativePart (ν : ℂ →₀ ℝ) : ℂ →₀ ℝ :=
  Finsupp.mapRange signedBudgetNeg signedBudgetNeg_zero ν

@[simp] theorem pointSignedPositivePart_apply (ν : ℂ →₀ ℝ) (x : ℂ) :
    pointSignedPositivePart ν x = signedBudgetPos (ν x) := rfl

@[simp] theorem pointSignedNegativePart_apply (ν : ℂ →₀ ℝ) (x : ℂ) :
    pointSignedNegativePart ν x = signedBudgetNeg (ν x) := rfl

/-- The support contains precisely the strictly positive atoms. -/
theorem mem_pointSignedPositivePart_support (ν : ℂ →₀ ℝ) (x : ℂ) :
    x ∈ (pointSignedPositivePart ν).support ↔ 0 < ν x := by
  rw [Finsupp.mem_support_iff, pointSignedPositivePart_apply]
  constructor
  · intro hx
    by_contra hn
    exact hx (max_eq_right (le_of_not_gt hn))
  · intro hx
    change max (ν x) 0 ≠ 0
    rw [max_eq_left hx.le]
    exact ne_of_gt hx

/-- The support contains precisely the strictly negative atoms. -/
theorem mem_pointSignedNegativePart_support (ν : ℂ →₀ ℝ) (x : ℂ) :
    x ∈ (pointSignedNegativePart ν).support ↔ ν x < 0 := by
  rw [Finsupp.mem_support_iff, pointSignedNegativePart_apply]
  constructor
  · intro hx
    by_contra hn
    exact hx (max_eq_right (neg_nonpos.mpr (le_of_not_gt hn)))
  · intro hx
    change max (-(ν x)) 0 ≠ 0
    rw [max_eq_left (neg_nonneg.mpr hx.le)]
    exact neg_ne_zero.mpr (ne_of_lt hx)

/-- No ambient point is identified with an atom index: collisions are coalesced
by the Finsupp representation, and zero coefficients have no support entry. -/
def pointSignedMarked (ν α : ℂ →₀ ℝ) : Finset ℂ := by
  classical
  exact ν.support ∪ α.support

@[simp] theorem mem_pointSignedMarked (ν α : ℂ →₀ ℝ) (x : ℂ) :
    x ∈ pointSignedMarked ν α ↔ ν x ≠ 0 ∨ α x ≠ 0 := by
  classical
  simp [pointSignedMarked, Finsupp.mem_support_iff]

theorem pointSigned_eq_zero_off_marked {ν α : ℂ →₀ ℝ} {x : ℂ}
    (hx : x ∉ pointSignedMarked ν α) : ν x = 0 ∧ α x = 0 := by
  classical
  simpa [mem_pointSignedMarked] using hx

/-- Support in an actual region remains an explicit, independently supplied
geometric fact. The algebra never chooses or postulates that region. -/
theorem pointSignedMarked_subset {ν α : ℂ →₀ ℝ} {P : Set ℂ}
    (hν : ∀ x, ν x ≠ 0 → x ∈ P) (hα : ∀ x, α x ≠ 0 → x ∈ P) :
    (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P := by
  intro x hx
  rcases (mem_pointSignedMarked ν α x).mp hx with hx | hx
  · exact hν x hx
  · exact hα x hx

/-- Curvature mass V; all finite sums use the honest common marked support. -/
def pointSignedCurvatureMass (ν α : ℂ →₀ ℝ) : ℝ :=
  ∑ x ∈ pointSignedMarked ν α, ν x

/-- Allocation mass A. -/
def pointSignedBudgetMass (ν α : ℂ →₀ ℝ) : ℝ :=
  ∑ x ∈ pointSignedMarked ν α, α x

def pointSignedPositiveMass (ν α : ℂ →₀ ℝ) : ℝ :=
  ∑ x ∈ pointSignedMarked ν α, signedBudgetPos (ν x)

def pointSignedNegativeMass (ν α : ℂ →₀ ℝ) : ℝ :=
  ∑ x ∈ pointSignedMarked ν α, signedBudgetNeg (ν x)

def pointSignedSurplusMass (ν α : ℂ →₀ ℝ) : ℝ :=
  ∑ x ∈ pointSignedMarked ν α, (α x - signedBudgetNeg (ν x))

/-- Positive mass away from an ambient point, including a point not marked. -/
def pointSignedPositiveMassAway (ν α : ℂ →₀ ℝ) (y : ℂ) : ℝ := by
  classical
  exact ∑ x ∈ (pointSignedMarked ν α).erase y, signedBudgetPos (ν x)

def pointSignedSurplusMassAway (ν α : ℂ →₀ ℝ) (y : ℂ) : ℝ := by
  classical
  exact ∑ x ∈ (pointSignedMarked ν α).erase y, (α x - signedBudgetNeg (ν x))

/-- Extending a finite curvature sum to the common support adds only zeroes. -/
theorem pointSigned_sum_marked_eq_support (ν α : ℂ →₀ ℝ)
    (g : ℝ → ℝ) (hg : g 0 = 0) :
    (∑ x ∈ pointSignedMarked ν α, g (ν x)) = ∑ x ∈ ν.support, g (ν x) := by
  classical
  apply Eq.symm
  apply Finset.sum_subset
  · exact Finset.subset_union_left
  · intro x hx hνx
    rw [Finsupp.notMem_support_iff.mp hνx, hg]

theorem pointSignedCurvatureMass_eq_support_sum (ν α : ℂ →₀ ℝ) :
    pointSignedCurvatureMass ν α = ∑ x ∈ ν.support, ν x :=
  pointSigned_sum_marked_eq_support ν α id rfl

theorem pointSignedBudgetMass_eq_support_sum (ν α : ℂ →₀ ℝ) :
    pointSignedBudgetMass ν α = ∑ x ∈ α.support, α x := by
  classical
  apply Eq.symm
  apply Finset.sum_subset
  · exact Finset.subset_union_right
  · intro x hx hαx
    exact Finsupp.notMem_support_iff.mp hαx

theorem pointSignedPositiveMass_eq_support_sum (ν α : ℂ →₀ ℝ) :
    pointSignedPositiveMass ν α = ∑ x ∈ ν.support, signedBudgetPos (ν x) :=
  pointSigned_sum_marked_eq_support ν α signedBudgetPos signedBudgetPos_zero

theorem pointSignedNegativeMass_eq_support_sum (ν α : ℂ →₀ ℝ) :
    pointSignedNegativeMass ν α = ∑ x ∈ ν.support, signedBudgetNeg (ν x) :=
  pointSigned_sum_marked_eq_support ν α signedBudgetNeg signedBudgetNeg_zero

/-- The Jordan decomposition identity for the signed total. -/
theorem pointSignedPositiveMass_sub_negativeMass (ν α : ℂ →₀ ℝ) :
    pointSignedPositiveMass ν α - pointSignedNegativeMass ν α =
      pointSignedCurvatureMass ν α := by
  unfold pointSignedPositiveMass pointSignedNegativeMass pointSignedCurvatureMass
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun x hx => signedBudgetPos_sub_neg (ν x))

theorem pointSignedSurplusMass_eq_budget_sub_negative (ν α : ℂ →₀ ℝ) :
    pointSignedSurplusMass ν α =
      pointSignedBudgetMass ν α - pointSignedNegativeMass ν α := by
  unfold pointSignedSurplusMass pointSignedBudgetMass pointSignedNegativeMass
  exact Finset.sum_sub_distrib _ _

/-- Splitting at any ambient point is valid, without assuming support membership. -/
theorem pointSignedPositiveMassAway_add (ν α : ℂ →₀ ℝ) (y : ℂ) :
    pointSignedPositiveMassAway ν α y + signedBudgetPos (ν y) =
      pointSignedPositiveMass ν α := by
  classical
  by_cases hy : y ∈ pointSignedMarked ν α
  · exact Finset.sum_erase_add _ _ hy
  · have hν := (pointSigned_eq_zero_off_marked hy).1
    simp [pointSignedPositiveMassAway, pointSignedPositiveMass,
      Finset.erase_eq_of_notMem hy, hν]

theorem pointSignedSurplusMassAway_add (ν α : ℂ →₀ ℝ) (y : ℂ) :
    pointSignedSurplusMassAway ν α y + (α y - signedBudgetNeg (ν y)) =
      pointSignedSurplusMass ν α := by
  classical
  by_cases hy : y ∈ pointSignedMarked ν α
  · exact Finset.sum_erase_add _ _ hy
  · obtain ⟨hν, hα⟩ := pointSigned_eq_zero_off_marked hy
    simp [pointSignedSurplusMassAway, pointSignedSurplusMass,
      Finset.erase_eq_of_notMem hy, hν, hα]

end RepulsiveCoulomb
