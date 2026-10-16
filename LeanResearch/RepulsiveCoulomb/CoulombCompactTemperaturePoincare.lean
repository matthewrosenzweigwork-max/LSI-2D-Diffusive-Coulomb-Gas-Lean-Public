import LeanResearch.RepulsiveCoulomb.CoulombTemperatureGapContradiction
import LeanResearch.RepulsiveCoulomb.CoulombFormCenter
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! RECORDS-ONLY UNCHECKED DRAFT. Fixed-particle Poincare constants uniform
on a compact positive temperature interval, on the full original form domain. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombForm_compact_temperature_coercivity (N : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : β ∈ Set.Icc a b),
      ∀ u : CoulombFormDomain N (ha.trans_le hβ.1),
        poleBranchRealMean N (ha.trans_le hβ.1)
          (coulombFormValueL N (ha.trans_le hβ.1) u) = 0 →
        ‖u‖ ≤ C * ‖coulombFormGradientL N (ha.trans_le hβ.1) u‖ := by
  classical
  by_contra hn
  push_neg at hn
  choose β hβ u hm hbad using fun n : ℕ => hn ((n : ℝ) + 1) (by positivity)
  have hne (n : ℕ) : u n ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_le_of_lt (mul_nonneg (by positivity) (norm_nonneg _)) (hbad n)
  let v : (n : ℕ) → CoulombFormDomain N (ha.trans_le (hβ n).1) :=
    fun n => (‖u n‖⁻¹ : ℝ) • u n
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) (hne n)
  have hvmean (n : ℕ) : poleBranchRealMean N (ha.trans_le (hβ n).1)
      (coulombFormValueL N (ha.trans_le (hβ n).1) (v n)) = 0 := by
    simp only [v, map_smul, hm n, smul_zero]
  have hvgrad (n : ℕ) : ‖coulombFormGradientL N (ha.trans_le (hβ n).1) (v n)‖ ≤
      1 / ((n : ℝ) + 1) := by
    have hp : 0 < ‖u n‖ := norm_pos_iff.mpr (hne n)
    have hh : ‖coulombFormGradientL N (ha.trans_le (hβ n).1) (u n)‖ / ‖u n‖ ≤
        1 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ hp (by positivity)).mpr
      nlinarith only [hbad n]
    simpa only [v, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (u n))), div_eq_inv_mul] using hh
  exact coulombTemperature_no_unit_meanZero_smallGradient ha hab β hβ v hvnorm hvmean hvgrad

theorem coulomb_compact_temperature_poincare (N : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : β ∈ Set.Icc a b),
      ∀ u : CoulombFormDomain (N + 2) (ha.trans_le hβ.1),
        variance (coulombFormValueL (N + 2) (ha.trans_le hβ.1) u :
          CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) ≤
        C * coulombFormEnergy (N + 2) (ha.trans_le hβ.1) u := by
  obtain ⟨C, hC, hc⟩ := coulombForm_compact_temperature_coercivity (N + 2) ha hab
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro β hβ u
  have hpos : 0 < β := ha.trans_le hβ.1
  have hco := hc β hβ (coulombFormCenter N hpos u) (coulombFormCenter_mean N hpos u)
  rw [coulombFormCenter_gradient] at hco
  have hval := coulombFormValue_norm_le (N + 2) hpos (coulombFormCenter N hpos u)
  have hs := (sq_le_sq₀ (norm_nonneg (coulombFormValueL (N + 2) hpos
    (coulombFormCenter N hpos u))) (mul_nonneg hC.le (norm_nonneg _))).mpr (hval.trans hco)
  rw [← coulombFormCenter_value_norm_sq N hpos u]
  simpa only [mul_pow, coulombFormEnergy] using hs

end RepulsiveCoulomb
