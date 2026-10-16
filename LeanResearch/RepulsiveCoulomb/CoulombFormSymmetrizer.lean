import LeanResearch.RepulsiveCoulomb.CoulombFormPermutation
import LeanResearch.RepulsiveCoulomb.CoulombSymmetrizer

/-! The actual symmetrizer preserves the full original form and does not increase its energy. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombFormSymmetrizer (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombFormDomain N hβ →L[ℝ] CoulombFormDomain N hβ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), coulombFormPermuteL N hβ σ

theorem coulombFormSymmetrizer_apply (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    coulombFormSymmetrizer N hβ u = (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), coulombFormPermuteL N hβ σ u := by
  simp [coulombFormSymmetrizer]

theorem coulombFormSymmetrizer_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u) =
      coulombSymmetrizer N hβ (coulombFormValueL N hβ u) := by
  rw [coulombFormSymmetrizer_apply, map_smul, map_sum, coulombSymmetrizer_apply]
  simp_rw [coulombFormPermuteL_value]

theorem coulombFormSymmetrizer_idempotent (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    coulombFormSymmetrizer N hβ (coulombFormSymmetrizer N hβ u) = coulombFormSymmetrizer N hβ u := by
  apply coulombFormValueL_injective N hβ
  simp only [coulombFormSymmetrizer_value, coulombSymmetrizer_idempotent]

theorem coulombFormSymmetrizer_invariant (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) (u : CoulombFormDomain N hβ) :
    coulombFormPermuteL N hβ σ (coulombFormSymmetrizer N hβ u) = coulombFormSymmetrizer N hβ u := by
  apply coulombFormValueL_injective N hβ
  simp only [coulombFormPermuteL_value, coulombFormSymmetrizer_value, coulombSymmetrizer_invariant]

theorem coulombFormSymmetrizer_gradient_norm_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    ‖coulombFormGradientL N hβ (coulombFormSymmetrizer N hβ u)‖ ≤ ‖coulombFormGradientL N hβ u‖ := by
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc0 : 0 ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ := by positivity
  rw [coulombFormSymmetrizer_apply, map_smul, map_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  calc
    _ ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ‖coulombFormGradientL N hβ (coulombFormPermuteL N hβ σ u)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc0
    _ = _ := by
      simp_rw [coulombFormPermuteL_gradient_norm]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem coulombFormSymmetrizer_energy_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    coulombFormEnergy N hβ (coulombFormSymmetrizer N hβ u) ≤ coulombFormEnergy N hβ u :=
  pow_le_pow_left₀ (norm_nonneg _) (coulombFormSymmetrizer_gradient_norm_le N hβ u) 2

theorem coulombForm_variance_permutation_decomposition (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) =
      variance (coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u) :
        CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) +
      ‖coulombFormValueL (N + 2) hβ u -
        coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u)‖ ^ 2 := by
  rw [coulombFormSymmetrizer_value]
  exact coulombSymmetrizer_variance_decomposition N hβ (coulombFormValueL (N + 2) hβ u)

end RepulsiveCoulomb

