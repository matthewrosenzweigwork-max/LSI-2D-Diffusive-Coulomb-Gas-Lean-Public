import LeanResearch.RepulsiveCoulomb.CoulombFormPairMaps

/-! All-label swap bound on the full original closed physical form. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombForm_all_pairs_swap_norm {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (i j : Fin (N + 2)), i ≠ j →
      ∀ u : CoulombFormDomain (N + 2) hβ,
      ‖coulombFormSwapDifferenceL (N + 2) hβ i j u‖ ^ 2 ≤
        (2 * P) * ‖coulombFormPairGradientL (N + 2) hβ i j u‖ ^ 2 := by
  obtain ⟨P, hP, hp⟩ := coulomb_core_all_pairs_swap_bound hβ
  refine ⟨P, hP, ?_⟩
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

theorem coulombFormSwapDifferenceL_norm_eq_integral (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (i j : Fin (N + 2)) (u : CoulombFormDomain (N + 2) hβ) :
    ‖coulombFormSwapDifferenceL (N + 2) hβ i j u‖ ^ 2 =
      ∫ z, (coulombFormValueL (N + 2) hβ u z -
        coulombFormValueL (N + 2) hβ u (coulombPermute (Equiv.swap i j) z)) ^ 2
          ∂coulombMeasure (N + 2) β := by
  rw [coulomb_L2_norm_sq N]
  apply integral_congr_ae
  filter_upwards [coulombFormSwapDifferenceL_coe (N + 2) hβ i j u] with z hz
  simp only [hz, Real.norm_eq_abs, sq_abs]

theorem coulombFormPairGradientL_norm_eq_integral (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (i j : Fin (N + 2)) (u : CoulombFormDomain (N + 2) hβ) :
    ‖coulombFormPairGradientL (N + 2) hβ i j u‖ ^ 2 =
      ∫ z, ‖coulombFormGradientL (N + 2) hβ u z i -
        coulombFormGradientL (N + 2) hβ u z j‖ ^ 2 ∂coulombMeasure (N + 2) β := by
  rw [coulomb_L2_norm_sq N]
  apply integral_congr_ae
  filter_upwards [coulombFormPairGradientL_coe (N + 2) hβ i j u] with z hz
  rw [hz]

theorem coulombForm_all_pairs_swap_integral {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (i j : Fin (N + 2)), i ≠ j →
      ∀ u : CoulombFormDomain (N + 2) hβ,
      (∫ z, (coulombFormValueL (N + 2) hβ u z -
        coulombFormValueL (N + 2) hβ u (coulombPermute (Equiv.swap i j) z)) ^ 2
          ∂coulombMeasure (N + 2) β) ≤
      (2 * P) * (∫ z, ‖coulombFormGradientL (N + 2) hβ u z i -
        coulombFormGradientL (N + 2) hβ u z j‖ ^ 2 ∂coulombMeasure (N + 2) β) := by
  obtain ⟨P, hP, hp⟩ := coulombForm_all_pairs_swap_norm hβ
  refine ⟨P, hP, ?_⟩
  intro N i j hij u
  have h := hp N i j hij u
  rwa [coulombFormSwapDifferenceL_norm_eq_integral, coulombFormPairGradientL_norm_eq_integral] at h

end RepulsiveCoulomb

