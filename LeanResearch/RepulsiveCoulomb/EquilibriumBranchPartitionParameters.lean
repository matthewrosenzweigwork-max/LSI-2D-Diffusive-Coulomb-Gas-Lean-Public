import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNelsonParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Particle-number-independent parameters for the actual partition tail
assembly. This specializes the already proved corrected integer construction;
the defective displayed source formulas are not reused. -/
noncomputable section
open Real
namespace RepulsiveCoulomb

/-- Sufficient exponents for exponential layer cake with the exact deterministic
coefficient (T/4)*log N. All choices precede N and beta. -/
theorem equilibriumPartition_parameters_exist (T : ℝ) :
    ∃ k m : ℕ, 2 ≤ k ∧ 1 ≤ m ∧ T + 1 < (k : ℝ) ∧
      T / 4 < 2 * (m : ℝ) - 1 ∧ Even (2 * k * m) ∧ 0 < 2 * k * m ∧
      0 < 4 * m ∧ 4 * m ≤ 2 * k * m := by
  obtain ⟨k, m, hk, hm, hpEven, hγ0, hγ1, hgap, hceil, hexponent⟩ :=
    equilibriumNelson_parameters_exist (T / 4) T (by norm_num : (0 : ℝ) < 2)
  rw [equilibriumNelson_floor_gap hk] at hgap
  rw [equilibriumNelson_moment_exponent hk hm] at hexponent
  have hkT : T + 1 < (k : ℝ) := by nlinarith
  have hkpos : 0 < k := by omega
  have hmpos : 0 < m := by omega
  have hp : 0 < 2 * k * m := by positivity
  have hq : 0 < 4 * m := by positivity
  have hqp : 4 * m ≤ 2 * k * m := by nlinarith
  exact ⟨k, m, hk, hm, hkT, hgap, hpEven, hp, hq, hqp⟩

/-- Exact high-moment ratio for the Hölder output in the specialized moment theorem. -/
theorem equilibriumPartition_order_ratio {k m : ℕ} (hm : 1 ≤ m) :
    ((2 * k * m : ℕ) : ℝ) / ((4 * m : ℕ) : ℝ) = (k : ℝ) / 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hm0]
  ring

/-- The radius factor after successive q-Hölder is exactly epsilon^k. No
loss from an independent-set selection or unused Hölder slots is inserted. -/
theorem equilibriumPartition_radius_power {k m : ℕ} (hm : 1 ≤ m)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    (C * ε ^ 2) ^ (((2 * k * m : ℕ) : ℝ) / ((4 * m : ℕ) : ℝ)) =
      C ^ ((k : ℝ) / 2) * ε ^ k := by
  rw [equilibriumPartition_order_ratio hm, Real.mul_rpow hC (sq_nonneg ε)]
  congr 1
  rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
  have he : (2 : ℝ) * ((k : ℝ) / 2) = (k : ℝ) := by ring
  simp only [Nat.cast_ofNat]
  rw [he, Real.rpow_natCast]

end RepulsiveCoulomb
