module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombLabels
public import LeanResearch.RepulsiveCoulomb.PointFormDefectiveLSI

@[expose] public section

/-!
One single positive K is chosen before every particle number, frozen
configuration and observable. Its core estimate is extended to the full
original one-site form and integrated into the physical particle core bound
without choosing another witness. rho_one=2/K is then merely a normalization
of this same constant. Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open PeriodicAttractiveLogGas
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_joint_one_site_constant {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (N : ℕ) (y : CoulombConfig N),
        ∀ u : PointFormDomain hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j),
        entropy (coulombOneSiteKernel N β hβ y)
          (fun w => (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w) ^ 2) ≤
          ((K * pointFormEnergy hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u : ℝ) : EReal)) ∧
      (∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
        (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
        (∀ i : Fin (N + 1), conditionalEntropyBranchCoulombSiteCost hβ
          (conditionalEntropyBranchCoulombCoreLaw β φ) i ≠ ∞) ∧
        (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
          (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
            ∂coulombMeasure (N + 1) β)) := by
  obtain ⟨K, hK, hk⟩ := pointCore_uniform_tight_lsi (Q := β) hβ
  refine ⟨K, hK, ?_, ?_⟩
  · intro N y u
    have hQ := (coulomb_one_site_exponent_sum_lt N hβ).le
    have h := pointForm_defective_lsi_of_core (C := K) (D := 0) hβ
      (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)
      (fun ψ => by
        simpa only [zero_mul, add_zero] using hk N (coulombOneSiteExponents N β)
          (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) hQ ψ) u
    simpa only [zero_mul, add_zero, coulombOneSiteKernel_apply] using h
  · have hOne : ∀ (N : ℕ) (y : CoulombConfig N)
        (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
        entropy (coulombOneSiteKernel N β hβ y) (fun w => φ (coulombInsertZero w y) ^ 2) ≤
          ((K * (∫ w, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2
            ∂coulombOneSiteKernel N β hβ y) : ℝ) : EReal) := by
      intro N y φ
      let a := coulombOneSiteExponents N β
      let ψ := coulombCoreSliceZero a φ y
      have h := hk N a (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)
        (coulomb_one_site_exponent_sum_lt N hβ).le ψ
      simpa only [ψ, coulombCoreSliceZero_apply, coulombCoreSliceZero_gradient,
        coulombOneSiteKernel_apply] using h
    exact conditionalEntropyBranch_coulomb_sum_core_upper_of_sites hβ K
      (conditionalEntropyBranch_coulomb_all_sites_core_upper_of_first hβ K
        (conditionalEntropyBranch_coulomb_first_core_upper_of_conditional hβ K hOne))

/-- The exact coefficient identities for the same K, never for a separately
chosen one-site witness. In particular the defective coefficient 2K is 4/rho. -/
theorem conditionalEntropyBranch_one_site_rate_normalization {K : ℝ} (hK : 0 < K) :
    0 < 2 / K ∧ 2 / (2 / K) = K ∧ 4 / (2 / K) = 2 * K := by
  refine ⟨div_pos (by norm_num) hK, ?_, ?_⟩ <;> field_simp [hK.ne'] <;> ring

end RepulsiveCoulomb
