import LeanResearch.RepulsiveCoulomb.CoulombCompactZeroGradientLimit
import LeanResearch.RepulsiveCoulomb.PoleBranchRealLpMean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! Compactness-to-coercivity adapter. The explicit zero-gradient mean-zero
kernel premise is a separate genuine input, not claimed proved by compactness. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombForm_coercivity_of_meanZero_kernel {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (hker : ∀ u : CoulombFormDomain N hβ,
      poleBranchRealMean N hβ (coulombFormValueL N hβ u) = 0 →
      coulombFormGradientL N hβ u = 0 → u = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoulombFormDomain N hβ,
      poleBranchRealMean N hβ (coulombFormValueL N hβ u) = 0 →
      ‖u‖ ≤ C * ‖coulombFormGradientL N hβ u‖ := by
  classical
  by_contra hn
  push_neg at hn
  choose u hm hbad using fun n : ℕ => hn ((n : ℝ) + 1) (by positivity)
  have hne (n : ℕ) : u n ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_le_of_lt (mul_nonneg (by positivity) (norm_nonneg _)) (hbad n)
  let v : ℕ → CoulombFormDomain N hβ := fun n => (‖u n‖⁻¹ : ℝ) • u n
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) (hne n)
  have hvmean (n : ℕ) : poleBranchRealMean N hβ (coulombFormValueL N hβ (v n)) = 0 := by
    simp only [v, map_smul, hm n, smul_zero]
  have hvgrad (n : ℕ) : ‖coulombFormGradientL N hβ (v n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    have hp : 0 < ‖u n‖ := norm_pos_iff.mpr (hne n)
    have hh : ‖coulombFormGradientL N hβ (u n)‖ / ‖u n‖ ≤ 1 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ hp (by positivity)).mpr
      nlinarith only [hbad n]
    simpa only [v, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (u n))), div_eq_inv_mul] using hh
  have hg : Tendsto (fun n => coulombFormGradientL N hβ (v n)) atTop (𝓝 0) :=
    squeeze_zero_norm hvgrad tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨w, σ, hσ, hw, hgw⟩ := coulombForm_subseq_zero_gradient hβ v 1
    (fun n => (hvnorm n).le) hg
  have hmzero : poleBranchRealMean N hβ (coulombFormValueL N hβ w) = 0 := by
    have ht := (((poleBranchRealMean N hβ).comp (coulombFormValueL N hβ)).continuous.tendsto w).comp hw
    have hz : Tendsto (fun n => poleBranchRealMean N hβ (coulombFormValueL N hβ (v (σ n))))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [hvmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht hz
  have hwzero := hker w hmzero hgw
  have hnorm : ‖w‖ = 1 := by
    have ht : Tendsto (fun n => ‖v (σ n)‖) atTop (𝓝 (1 : ℝ)) := by
      simpa only [hvnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hw.norm ht
  rw [hwzero, norm_zero] at hnorm
  norm_num at hnorm

end RepulsiveCoulomb
