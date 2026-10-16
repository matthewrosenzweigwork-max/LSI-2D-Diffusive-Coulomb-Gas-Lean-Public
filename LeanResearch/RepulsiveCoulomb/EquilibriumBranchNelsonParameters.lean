import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogKernel
import Mathlib.Algebra.Order.Floor.Ring

/-! Exact auxiliary integer choices for the repulsive partition tail argument.
The displayed choices in the cited paper do not imply their asserted strict
floor bound. This replacement preserves the intended analytic theorem, gives
an even moment order, and is explicitly independent of particle number N. -/
noncomputable section
open Real
namespace RepulsiveCoulomb

def equilibriumNelsonOrder (k m : ℕ) : ℕ := 2 * k * m

def equilibriumNelsonGamma (k : ℕ) : ℝ := ((k : ℝ) - 1) / (k : ℝ)

theorem equilibriumNelsonOrder_even (k m : ℕ) : Even (equilibriumNelsonOrder k m) := by
  refine ⟨k * m, ?_⟩
  unfold equilibriumNelsonOrder
  ring

theorem equilibriumNelsonGamma_range {k : ℕ} (hk : 2 ≤ k) :
    (1 / 2 : ℝ) ≤ equilibriumNelsonGamma k ∧ equilibriumNelsonGamma k < 1 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  unfold equilibriumNelsonGamma
  constructor
  · rw [le_div_iff₀ hk0]
    linarith
  · rw [div_lt_iff₀ hk0]
    linarith

/-- The splitting threshold is exactly integral, eliminating floor/ceiling ambiguity. -/
theorem equilibriumNelsonGamma_mul_order {k m : ℕ} (hk : 2 ≤ k) :
    equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ) =
      ((2 * (k - 1) * m : ℕ) : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [equilibriumNelsonGamma, equilibriumNelsonOrder, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sub hk1, Nat.cast_one]
  field_simp [hk0]

theorem equilibriumNelson_floor {k m : ℕ} (hk : 2 ≤ k) :
    ⌊equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌋ =
      (2 * (k - 1) * m : ℕ) := by
  rw [equilibriumNelsonGamma_mul_order hk, Int.floor_natCast]

theorem equilibriumNelson_ceil {k m : ℕ} (hk : 2 ≤ k) :
    ⌈equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌉ =
      (2 * (k - 1) * m : ℕ) := by
  rw [equilibriumNelsonGamma_mul_order hk, Int.ceil_natCast]

theorem equilibriumNelson_floor_gap {k m : ℕ} (hk : 2 ≤ k) :
    (equilibriumNelsonOrder k m : ℝ) - 1 -
      (⌊equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌋ : ℤ) =
        2 * (m : ℝ) - 1 := by
  rw [equilibriumNelson_floor hk]
  simp only [equilibriumNelsonOrder, Int.cast_natCast, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  push_cast
  ring

theorem equilibriumNelson_ceil_gap {k m : ℕ} (hk : 2 ≤ k) :
    (equilibriumNelsonOrder k m : ℝ) -
      (⌈equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌉ : ℤ) =
        2 * (m : ℝ) := by
  rw [equilibriumNelson_ceil hk]
  simp only [equilibriumNelsonOrder, Int.cast_natCast, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  push_cast
  ring

theorem equilibriumNelson_moment_exponent {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    (κ : ℝ) :
    κ * (equilibriumNelsonOrder k m : ℝ) /
      (2 * ((equilibriumNelsonOrder k m : ℝ) -
        (⌈equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌉ : ℤ))) =
      κ * (k : ℝ) / 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [equilibriumNelson_ceil_gap hk]
  simp only [equilibriumNelsonOrder, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hm0]

/-- Parameters precede and are independent of N. Positive kappa is the only
necessary restriction; in the partition application C1,C2 are nonnegative. -/
theorem equilibriumNelson_parameters_exist (C₁ C₂ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ k m : ℕ, 2 ≤ k ∧ 1 ≤ m ∧ Even (equilibriumNelsonOrder k m) ∧
      (1 / 2 : ℝ) ≤ equilibriumNelsonGamma k ∧ equilibriumNelsonGamma k < 1 ∧
      C₁ < (equilibriumNelsonOrder k m : ℝ) - 1 -
        (⌊equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌋ : ℤ) ∧
      1 ≤ (equilibriumNelsonOrder k m : ℝ) -
        (⌈equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌉ : ℤ) ∧
      C₂ + 1 < κ * (equilibriumNelsonOrder k m : ℝ) /
        (2 * ((equilibriumNelsonOrder k m : ℝ) -
          (⌈equilibriumNelsonGamma k * (equilibriumNelsonOrder k m : ℝ)⌉ : ℤ))) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max (1 : ℝ) (2 * (C₂ + 1) / κ))
  have hk1r : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk2 : 2 ≤ k := by
    have hk1 : 1 < k := by exact_mod_cast hk1r
    omega
  have hkex : C₂ + 1 < κ * (k : ℝ) / 2 := by
    have h := (le_max_right (1 : ℝ) (2 * (C₂ + 1) / κ)).trans_lt hk
    rw [div_lt_iff₀ hκ] at h
    nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (max (0 : ℝ) ((C₁ + 1) / 2))
  have hm0r : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm1 : 1 ≤ m := by
    have hm0 : 0 < m := by exact_mod_cast hm0r
    omega
  have hmex : C₁ < 2 * (m : ℝ) - 1 := by
    have h := (le_max_right (0 : ℝ) ((C₁ + 1) / 2)).trans_lt hm
    linarith
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  obtain ⟨hγ0, hγ1⟩ := equilibriumNelsonGamma_range hk2
  refine ⟨k, m, hk2, hm1, equilibriumNelsonOrder_even k m, hγ0, hγ1, ?_, ?_, ?_⟩
  · rw [equilibriumNelson_floor_gap hk2]
    exact hmex
  · rw [equilibriumNelson_ceil_gap hk2]
    linarith
  · rw [equilibriumNelson_moment_exponent hk2 hm1]
    exact hkex

end RepulsiveCoulomb
