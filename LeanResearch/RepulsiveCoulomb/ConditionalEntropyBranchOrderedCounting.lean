import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
Exact finite ordered-pair counting for the manuscript's conditional potential.
The diagonal is omitted explicitly. No symmetry or distinct-position premise
is used by this algebraic identity; physical density identities still require
their separate off-collision/a.e. justification.
Records-only draft, not staged or checked.
-/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_offDiagonal_row {N : ℕ} (u : Fin N → ℝ) (i : Fin N) :
    (∑ j, if i = j then 0 else u j) = (∑ j, u j) - u i := by
  classical
  have he (j : Fin N) : (if i = j then (0 : ℝ) else u j) =
      u j - (if i = j then u i else 0) := by
    by_cases h : i = j
    · subst j
      simp
    · simp only [h, if_false, sub_zero]
  simp_rw [he, Finset.sum_sub_distrib]
  simp

theorem conditionalEntropyBranch_offDiagonal_columns {N : ℕ} (u : Fin N → ℝ) :
    (∑ i, ∑ j, if i = j then 0 else u j) = ((N : ℝ) - 1) * ∑ j, u j := by
  simp_rw [conditionalEntropyBranch_offDiagonal_row, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- If Phi_i(x_i) = row(g)/N-U_i and its reference mean is row(U)/N-c,
their centered sum is exactly 2 A_N + (sum U)/N. -/
theorem conditionalEntropyBranch_ordered_pair_identity {N : ℕ} (hN : 0 < N)
    (H : Fin N → Fin N → ℝ) (u : Fin N → ℝ) (c : ℝ) :
    (∑ i, (((∑ j, if i = j then 0 else H i j) / (N : ℝ) - u i) -
      ((∑ j, if i = j then 0 else u j) / (N : ℝ) - c))) =
      2 * ((∑ i, ∑ j, if i = j then 0 else H i j) / (2 * (N : ℝ)) -
        (∑ i, u i) + (N : ℝ) * c / 2) + (∑ i, u i) / (N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [conditionalEntropyBranch_offDiagonal_columns]
  field_simp [hn] <;> ring

end RepulsiveCoulomb
