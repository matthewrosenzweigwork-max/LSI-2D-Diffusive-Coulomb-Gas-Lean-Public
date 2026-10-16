import LeanResearch.RepulsiveCoulomb.CoulombCompactMeanZeroCoercivity
import LeanResearch.RepulsiveCoulomb.CoulombFormCenter
import LeanResearch.RepulsiveCoulomb.CoulombFormInner

/-! Fixed-particle Poincare assembly from an independently proved kernel
input. This adapter does not claim the kernel premise has been discharged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb

theorem coulombForm_poincare_of_meanZero_kernel (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (hker : ∀ u : CoulombFormDomain (N + 2) hβ,
      poleBranchRealMean (N + 2) hβ (coulombFormValueL (N + 2) hβ u) = 0 →
      coulombFormGradientL (N + 2) hβ u = 0 → u = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoulombFormDomain (N + 2) hβ,
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤ C * coulombFormEnergy (N + 2) hβ u := by
  obtain ⟨C, hC, hbound⟩ := coulombForm_coercivity_of_meanZero_kernel hβ hker
  refine ⟨C ^ 2, sq_pos_of_pos hC, fun u => ?_⟩
  have hb := hbound (coulombFormCenter N hβ u) (coulombFormCenter_mean N hβ u)
  rw [coulombFormCenter_gradient] at hb
  rw [← coulombFormCenter_value_norm_sq N hβ u]
  calc
    _ ≤ ‖coulombFormCenter N hβ u‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (coulombFormValueL_norm_le (N + 2) hβ (coulombFormCenter N hβ u))
    _ ≤ (C * ‖coulombFormGradientL (N + 2) hβ u‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr hb
    _ = C ^ 2 * coulombFormEnergy (N + 2) hβ u := by rw [mul_pow]; rfl

end RepulsiveCoulomb
