import LeanResearch.RepulsiveCoulomb.CoulombRelativeRoots

/-! Exact relative-coordinate factorization of the original particle density. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombRelativeInsert_eq_double {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeInsert c u y =
      coulombInsertZero ((Real.sqrt 2)⁻¹ • (c + u))
        (coulombInsertZero ((Real.sqrt 2)⁻¹ • (c - u)) y) := by
  ext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

theorem norm_real_smul_rpow (s α : ℝ) (hs : 0 ≤ s) (z : ℂ) :
    ‖s • z‖ ^ α = s ^ α * ‖z‖ ^ α := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, Real.mul_rpow hs (norm_nonneg z)]

def coulombRelativeScale (N : ℕ) (α : ℝ) : ℝ :=
  (Real.sqrt 2) ^ α * ((∏ _ : Fin N, ((Real.sqrt 2)⁻¹) ^ α) *
    (∏ _ : Fin N, ((Real.sqrt 2)⁻¹) ^ α))

theorem coulombRelativeScale_pos (N : ℕ) (α : ℝ) : 0 < coulombRelativeScale N α := by
  unfold coulombRelativeScale
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact mul_pos (Real.rpow_pos_of_pos hs _) (mul_pos
    (Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos (inv_pos.mpr hs) _))
    (Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos (inv_pos.mpr hs) _)))

theorem coulombRelative_interaction {N : ℕ} (α : ℝ) (c u : ℂ) (y : CoulombConfig N) :
    coulombInteraction α (coulombRelativeInsert c u y) =
      coulombRelativeScale N α * coulombInteraction α y * ‖u‖ ^ α *
        ((∏ j, ‖u - (Real.sqrt 2 • y j - c)‖ ^ α) *
          ∏ j, ‖u + (Real.sqrt 2 • y j - c)‖ ^ α) := by
  have hp := coulombRelative_pair_difference c u y
  have hl := coulombRelative_left_difference c u y
  have hr := coulombRelative_right_difference c u y
  simp only [coulombRelativeInsert_zero, coulombRelativeInsert_one,
    coulombRelativeInsert_succ_succ] at hp hl hr
  rw [coulombRelativeInsert_eq_double, coulombInteraction_insert_zero,
    coulombInteraction_insert_zero, Fin.prod_univ_succ]
  simp only [coulombInsertZero_zero, coulombInsertZero_succ]
  rw [hp, norm_real_smul_rpow _ _ (Real.sqrt_nonneg 2)]
  simp_rw [hl, hr, norm_neg,
    norm_real_smul_rpow _ _ (inv_nonneg.mpr (Real.sqrt_nonneg 2))]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold coulombRelativeScale
  ring

theorem coulombWeight_relative_factorization {N : ℕ} (β : ℝ) (c u : ℂ) (y : CoulombConfig N) :
    coulombWeight β (coulombRelativeInsert c u y) =
      (coulombRelativeScale N (β / ((N + 2 : ℕ) : ℝ)) *
        Real.exp (-β * ‖c‖ ^ 2 / 2) *
        coulombWeightAtExponent β (β / ((N + 2 : ℕ) : ℝ)) y) *
      pointWeight β (fun _ : Fin (N + N + 1) => β / ((N + 2 : ℕ) : ℝ))
        (coulombRelativeRoots c y) u := by
  rw [coulombWeight_eq_atExponent, coulombWeightAtExponent,
    coulombRelativeInsert_norm_sq, coulombRelative_interaction, coulombRelative_pointWeight]
  have he : Real.exp (-β * (‖c‖ ^ 2 + (‖u‖ ^ 2 + ‖y‖ ^ 2)) / 2) =
      Real.exp (-β * ‖c‖ ^ 2 / 2) * Real.exp (-β * ‖u‖ ^ 2 / 2) *
        Real.exp (-β * ‖y‖ ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold coulombWeightAtExponent
  ring

end RepulsiveCoulomb

