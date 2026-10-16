module

public import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalSymmetricConstant
public import LeanResearch.RepulsiveCoulomb.PoleBranchSymmetricPIAssembly

@[expose] public section

/-! RECORDS-ONLY UNCOMPILED CONDITIONAL APPLICATION. The exact manuscript
C_sym is admissible on the original symmetric full form if the still-open
original-core dbar distance estimate is supplied. Small particle numbers use
actual optimal C_P, while the complementary range uses the exact 1/beta bound.
This file does not prove the dbar premise or complete symmetric PI. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb

theorem poleBranch_optimal_symmetric_pi_of_dbar_distance {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 < β)
    (hdist : ∀ ψ : TestFunction (coulombDomain N) ℂ ⊤,
      ‖coulombComplexCoreValue hβ ψ -
        coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ)‖ ^ 2 ≤
          (2 / β) * ‖coulombComplexCoreDbar hβ ψ‖ ^ 2)
    (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      poleBranchSymmetricPoincareConstant hβ * coulombFormEnergy N hβ u := by
  by_cases hsmall : (N : ℝ) ≤ β / 2
  · have hmem := (poleBranchExceptionalParticleCounts_mem hβ.le N).mpr ⟨hN, hsmall⟩
    have hcp := poleBranchSymmetricPoincareConstant_optimal_le hβ N hmem
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
    exact (coulombOptimalPoincare_inequality n hβ u).trans
      (mul_le_mul_of_nonneg_right hcp (coulombFormEnergy_nonneg (n + 2) hβ u))
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have ha2 : β / (N : ℝ) ≤ 2 := (div_le_iff₀ hNpos).mpr (by linarith)
    exact (poleBranch_symmetric_form_pi_of_dbar_distance hβ ha2 hdist u hsym).trans
      (mul_le_mul_of_nonneg_right (poleBranchSymmetricPoincareConstant_one_div_le hβ)
        (coulombFormEnergy_nonneg N hβ u))

theorem poleBranch_optimal_symmetrized_pi_of_dbar_distance {N : ℕ} (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 < β)
    (hdist : ∀ ψ : TestFunction (coulombDomain N) ℂ ⊤,
      ‖coulombComplexCoreValue hβ ψ -
        coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ)‖ ^ 2 ≤
          (2 / β) * ‖coulombComplexCoreDbar hβ ψ‖ ^ 2)
    (u : CoulombFormDomain N hβ) :
    variance (coulombSymmetrizer N hβ (coulombFormValueL N hβ u) : CoulombConfig N → ℝ)
      (coulombMeasure N β) ≤
      poleBranchSymmetricPoincareConstant hβ * coulombFormEnergy N hβ u := by
  have hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ
          (coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u)) =
        coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u) := by
    intro σ
    rw [coulombFormSymmetrizer_value]
    exact coulombSymmetrizer_invariant N hβ σ _
  have h := poleBranch_optimal_symmetric_pi_of_dbar_distance hN hβ hdist
    (coulombFormSymmetrizer N hβ u) hsym
  rw [coulombFormSymmetrizer_value] at h
  exact h.trans (mul_le_mul_of_nonneg_left (coulombFormSymmetrizer_energy_le N hβ u)
    (poleBranchSymmetricPoincareConstant_pos hβ).le)

end RepulsiveCoulomb
