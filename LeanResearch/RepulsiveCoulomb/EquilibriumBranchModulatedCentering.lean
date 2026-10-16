module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel

@[expose] public section

/-! Exact ordered-pair normalization of the manuscript's modulated energy.
The centered U-statistic differs from A_N by a surviving one-body correction.
This module does not assume or assert any partition bound. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumOrderedOffDiagonalSum {N : ℕ} (H : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else H i j

theorem equilibriumOffDiagonal_oneBody {N : ℕ} (u : Fin N → ℝ) :
    equilibriumOrderedOffDiagonalSum (fun i j => u i + u j) =
      2 * ((N : ℝ) - 1) * ∑ i, u i := by
  classical
  have he (i j : Fin N) : (if i = j then (0 : ℝ) else u i + u j) =
      (u i + u j) - (if i = j then 2 * u i else 0) := by
    split_ifs with h
    · subst j
      ring
    · ring
  unfold equilibriumOrderedOffDiagonalSum
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum]
  ring

theorem equilibriumOffDiagonal_const (N : ℕ) (c : ℝ) :
    equilibriumOrderedOffDiagonalSum (N := N) (fun _ _ => c) =
      (N : ℝ) * ((N : ℝ) - 1) * c := by
  classical
  have he (i j : Fin N) : (if i = j then (0 : ℝ) else c) = c - (if i = j then c else 0) := by
    split_ifs <;> ring
  unfold equilibriumOrderedOffDiagonalSum
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem equilibriumOffDiagonal_centered {N : ℕ} (H : Fin N → Fin N → ℝ)
    (u : Fin N → ℝ) (c : ℝ) :
    equilibriumOrderedOffDiagonalSum (fun i j => H i j - u i - u j + c) =
      equilibriumOrderedOffDiagonalSum H - 2 * ((N : ℝ) - 1) * (∑ i, u i) +
        (N : ℝ) * ((N : ℝ) - 1) * c := by
  have he : equilibriumOrderedOffDiagonalSum (fun i j => H i j - u i - u j + c) =
      equilibriumOrderedOffDiagonalSum H -
        equilibriumOrderedOffDiagonalSum (fun i j => u i + u j) +
          equilibriumOrderedOffDiagonalSum (N := N) (fun _ _ => c) := by
    unfold equilibriumOrderedOffDiagonalSum
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [he, equilibriumOffDiagonal_oneBody, equilibriumOffDiagonal_const]

/-- The exact manuscript normalization, including its c/2 correction. -/
theorem equilibrium_modulated_centering {N : ℕ} (hN : 0 < N)
    (H : Fin N → Fin N → ℝ) (u : Fin N → ℝ) (c : ℝ) :
    equilibriumOrderedOffDiagonalSum H / (2 * (N : ℝ)) - (∑ i, u i) + (N : ℝ) * c / 2 =
      equilibriumOrderedOffDiagonalSum (fun i j => H i j - u i - u j + c) / (2 * (N : ℝ)) -
        (∑ i, u i) / (N : ℝ) + c / 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [equilibriumOffDiagonal_centered]
  field_simp [hn]
  ring

end RepulsiveCoulomb
