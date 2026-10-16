module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeGeometry

@[expose] public section

/-! Literal locations in the relative conditional; coincident roots are retained. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombRelativeRoots {N : ℕ} (c : ℂ) (y : CoulombConfig N) : Fin (N + N + 1) → ℂ :=
  Fin.cons 0 (Fin.append (fun j => Real.sqrt 2 • y j - c)
    (fun j => -(Real.sqrt 2 • y j - c)))

theorem coulombRelativeRoots_zero {N : ℕ} (c : ℂ) (y : CoulombConfig N) :
    coulombRelativeRoots c y 0 = 0 := rfl

theorem coulombRelativeRoots_left {N : ℕ} (c : ℂ) (y : CoulombConfig N) (j : Fin N) :
    coulombRelativeRoots c y (j.castAdd N).succ = Real.sqrt 2 • y j - c := by
  simp only [coulombRelativeRoots, Fin.cons_succ, Fin.append_left, Fin.append_right]

theorem coulombRelativeRoots_right {N : ℕ} (c : ℂ) (y : CoulombConfig N) (j : Fin N) :
    coulombRelativeRoots c y (Fin.natAdd N j).succ = -(Real.sqrt 2 • y j - c) := by
  simp only [coulombRelativeRoots, Fin.cons_succ, Fin.append_left, Fin.append_right]

theorem coulombRelative_pointWeight {N : ℕ} (γ α : ℝ) (c u : ℂ) (y : CoulombConfig N) :
    pointWeight γ (fun _ : Fin (N + N + 1) => α) (coulombRelativeRoots c y) u =
      Real.exp (-γ * ‖u‖ ^ 2 / 2) * ‖u‖ ^ α *
        ((∏ j, ‖u - (Real.sqrt 2 • y j - c)‖ ^ α) *
          ∏ j, ‖u + (Real.sqrt 2 • y j - c)‖ ^ α) := by
  simp only [pointWeight, coulombRelativeRoots, Fin.prod_univ_succ, Fin.cons_zero,
    sub_zero, Fin.cons_succ, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    sub_neg_eq_add]
  ring

theorem sqrt_two_inv_twice : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  field_simp
  nlinarith

theorem coulombRelative_pair_difference {N : ℕ} (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeInsert c u y 0 - coulombRelativeInsert c u y (Fin.succ 0) =
      Real.sqrt 2 • u := by
  rw [coulombRelativeInsert_zero, coulombRelativeInsert_one]
  calc
    _ = ((Real.sqrt 2)⁻¹ * 2) • u := by module
    _ = _ := by rw [sqrt_two_inv_twice]

theorem coulombRelative_left_difference {N : ℕ} (c u : ℂ) (y : CoulombConfig N) (j : Fin N) :
    coulombRelativeInsert c u y 0 - coulombRelativeInsert c u y j.succ.succ =
      (Real.sqrt 2)⁻¹ • (u - (Real.sqrt 2 • y j - c)) := by
  rw [coulombRelativeInsert_zero, coulombRelativeInsert_succ_succ]
  have hs : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 := inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num)).ne'
  simp only [smul_sub, smul_add, smul_smul, hs, one_smul]
  abel

theorem coulombRelative_right_difference {N : ℕ} (c u : ℂ) (y : CoulombConfig N) (j : Fin N) :
    coulombRelativeInsert c u y (Fin.succ 0) - coulombRelativeInsert c u y j.succ.succ =
      -((Real.sqrt 2)⁻¹ • (u + (Real.sqrt 2 • y j - c))) := by
  rw [coulombRelativeInsert_one, coulombRelativeInsert_succ_succ]
  have hs : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 := inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num)).ne'
  simp only [smul_sub, smul_add, smul_smul, hs, one_smul]
  abel

theorem coulombRelative_exponent_sum_lt (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∑ _ : Fin (N + N + 1), β / ((N + 2 : ℕ) : ℝ)) < 2 * β := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < ((N + 2 : ℕ) : ℝ))]
  push_cast
  nlinarith

end RepulsiveCoulomb

