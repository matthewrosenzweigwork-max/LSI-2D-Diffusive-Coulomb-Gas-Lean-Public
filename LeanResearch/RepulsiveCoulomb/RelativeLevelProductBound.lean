import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The exact elementary bridge from relative isoperimetry to the product of
strict level-side masses in double layer cake. -/
namespace RepulsiveCoulomb

theorem relative_level_product_bound {A B M C L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hAM : A ≤ M) (hBM : B ≤ M) (hiso : min A B ≤ C * L^2) :
    A * B ≤ M * Real.sqrt (M*C) * L := by
  have hm0 : 0 ≤ min A B := le_min hA hB
  have hmM : min A B ≤ M := (min_le_left _ _).trans hAM
  have hsq : (min A B)^2 ≤ M * (C * L^2) := by
    have hh : (min A B)^2 ≤ M * min A B := by nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_left hiso hM)
  have hs0 : 0 ≤ Real.sqrt (M*C) * L := mul_nonneg (Real.sqrt_nonneg _) hL
  have hs : (Real.sqrt (M*C) * L)^2 = M * (C * L^2) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hM hC)]
    ring
  have hmin : min A B ≤ Real.sqrt (M*C) * L := by nlinarith
  have hprod : A*B ≤ M * min A B := by
    rcases le_total A B with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  exact hprod.trans (by nlinarith [mul_le_mul_of_nonneg_left hmin hM])

end RepulsiveCoulomb
