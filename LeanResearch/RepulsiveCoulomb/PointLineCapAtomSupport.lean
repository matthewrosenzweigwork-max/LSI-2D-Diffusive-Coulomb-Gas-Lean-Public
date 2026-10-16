module

public import LeanResearch.RepulsiveCoulomb.PointLineCapBoundedSide
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Records-only, uncompiled. Atomic boundary support is already stable for
EVERY sufficiently large actual cap, independently of the unresolved global
left/right identification. No atomic mass or allocation is assumed. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- An enclosed point belongs to the cap boundary exactly when it belongs to
the actual complete line. This includes coincident atoms and zero exponents. -/
theorem lineCap_boundary_membership_inside_circle {c : ℝ → ℂ} {tm tp R α β : ℝ}
    (hR : 0 < R) (hinside : ∀ t, ‖c t‖ < R ↔ t ∈ Ioo tm tp)
    {z : ℂ} (hz : ‖z‖ < R) :
    z ∈ c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1 ↔ z ∈ range c := by
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact mem_range_self t
    · rw [pointCircleCapArc_norm hR.le] at hz
      exact False.elim (lt_irrefl _ hz)
  · rintro ⟨t, rfl⟩
    have ht := (hinside t).mp hz
    exact Or.inl ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩

/-- One explicit common radius encloses the entire finite location list. -/
theorem lineCap_all_atoms_below_radius {m : ℕ} (y : Fin m → ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ R, A ≤ R → ∀ j, ‖y j‖ < R := by
  let A := 1 + ∑ j, ‖y j‖
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro R hR j
  have hsum : ‖y j‖ ≤ ∑ i, ‖y i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg (y i)) (Finset.mem_univ j)
  dsimp [A] at hR
  linarith

/-- Literal finite boundary membership stabilizes; no weak convergence of
atomic allocations is used. This is boundary SUPPORT stability only. -/
theorem lineCap_atomic_boundary_support_stable {m : ℕ} (y : Fin m → ℂ)
    {c : ℝ → ℂ} {tm tp R α β : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hinside : ∀ t, ‖c t‖ < R ↔ t ∈ Ioo tm tp)
    (hatoms : ∀ j, ‖y j‖ < R)
    (hfront : frontier U = c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1) :
    ∀ j, y j ∈ frontier U ↔ y j ∈ range c := by
  intro j
  rw [hfront]
  exact lineCap_boundary_membership_inside_circle hR hinside (hatoms j)

/-- The same pointwise identity gives exact weighted boundary selectors for
any coefficients. This does not identify physical side-angle coefficients. -/
theorem lineCap_atomic_boundary_selector_stable {m : ℕ} (y : Fin m → ℂ)
    (w : Fin m → ℝ) {c : ℝ → ℂ} {tm tp R α β : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hinside : ∀ t, ‖c t‖ < R ↔ t ∈ Ioo tm tp)
    (hatoms : ∀ j, ‖y j‖ < R)
    (hfront : frontier U = c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1) :
    (∑ j, if y j ∈ frontier U then w j else 0) =
      ∑ j, if y j ∈ range c then w j else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  rw [lineCap_atomic_boundary_support_stable y hR hinside hatoms hfront j]

end RepulsiveCoulomb
