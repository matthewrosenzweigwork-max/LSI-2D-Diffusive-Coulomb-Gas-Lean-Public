import LeanResearch.RepulsiveCoulomb.PointDilationBranchNamedSwapTransport
import LeanResearch.RepulsiveCoulomb.CoulombFormSwap

/-! RECORDS-ONLY UNCOMPILED. The supplied constant is preserved through
actual label permutations and original-core closure to the full physical form. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointDilationBranch_all_pairs_swap_of_first {β P : ℝ} (hβ : 0 < β)
    (hp : ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      (∫ z, (φ z - φ (coulombSwapFirst N z)) ^ 2 ∂coulombMeasure (N + 2) β) ≤
        (2 * P) * (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z 0 -
          gradient (φ : CoulombConfig (N + 2) → ℝ) z (Fin.succ 0)‖ ^ 2
            ∂coulombMeasure (N + 2) β)) :
    ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤)
      (i j : Fin (N + 2)), i ≠ j →
      (∫ z, (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2 ∂coulombMeasure (N + 2) β) ≤
        (2 * P) * (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z i -
          gradient (φ : CoulombConfig (N + 2) → ℝ) z j‖ ^ 2 ∂coulombMeasure (N + 2) β) := by
  intro N φ i j hij
  obtain ⟨σ, hσ0, hσ1⟩ := exists_coulomb_pair_permutation i j hij
  have h := hp N (coulombPermuteCore σ.symm φ)
  have hswap (z : CoulombConfig (N + 2)) :
      coulombPermute σ.symm (coulombSwapFirst N z) =
        coulombPermute (Equiv.swap i j) (coulombPermute σ.symm z) := by
    rw [coulombSwapFirst_eq_permute, coulombPermute_swap_conjugacy]
    simp only [Equiv.symm_symm, hσ0, hσ1]
  simp only [coulombPermuteCore_apply, coulombPermuteCore_gradient_component,
    Equiv.symm_symm, hσ0, hσ1, hswap] at h
  have hm := coulombPermute_gibbs_preserving hβ.le σ.symm
  have hF := hm.integral_comp (coulombPermute σ.symm).toMeasurableEquiv.measurableEmbedding
    (fun z => (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2)
  have hG := hm.integral_comp (coulombPermute σ.symm).toMeasurableEquiv.measurableEmbedding
    (fun z => ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z i -
      gradient (φ : CoulombConfig (N + 2) → ℝ) z j‖ ^ 2)
  rw [hF, hG] at h
  exact h

theorem pointDilationBranch_form_swap_of_core {β P : ℝ} (hβ : 0 < β)
    (hp : ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤)
      (i j : Fin (N + 2)), i ≠ j →
      (∫ z, (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2 ∂coulombMeasure (N + 2) β) ≤
        (2 * P) * (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z i -
          gradient (φ : CoulombConfig (N + 2) → ℝ) z j‖ ^ 2 ∂coulombMeasure (N + 2) β)) :
    ∀ (N : ℕ) (i j : Fin (N + 2)), i ≠ j →
      ∀ u : CoulombFormDomain (N + 2) hβ,
      ‖coulombFormSwapDifferenceL (N + 2) hβ i j u‖ ^ 2 ≤
        (2 * P) * ‖coulombFormPairGradientL (N + 2) hβ i j u‖ ^ 2 := by
  intro N i j hij u
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation (N + 2) hβ u
  have hl := (((coulombFormSwapDifferenceL (N + 2) hβ i j).continuous.norm.pow 2).tendsto u).comp hφ
  have hr := (((coulombFormPairGradientL (N + 2) hβ i j).continuous.norm.pow 2).tendsto u).comp hφ
  apply le_of_tendsto_of_tendsto hl (tendsto_const_nhds.mul hr)
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply, Pi.pow_apply]
  rw [coulombFormSwapDifferenceL_core_norm, coulombFormPairGradientL_core_norm]
  exact hp N (φ n) i j hij

end RepulsiveCoulomb
