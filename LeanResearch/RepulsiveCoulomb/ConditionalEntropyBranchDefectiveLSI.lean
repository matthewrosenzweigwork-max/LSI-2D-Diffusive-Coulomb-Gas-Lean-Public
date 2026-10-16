import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchUniformDefect
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchOneSiteWitness
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoreClosure

/-!
Source-level defective LSI from the actual conditional-entropy chain. The same
one-site K gives 2K in the defective estimate, and the literal supremum defect
gives 2D. Core normalization is zero-safe; closure is on the original complete
physical form. The analytic dependency chain is uncompiled, so this file is
not a checked theorem or a main-theorem acceptance claim.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open PeriodicAttractiveLogGas
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_B_core_integrable {N : ℕ} {β : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (conditionalEntropyBranchThermalB R) (conditionalEntropyBranchCoulombCoreLaw β φ) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hB := conditionalEntropyBranch_B_gibbs_integrable hN hβ R
  obtain ⟨M, hMpos, hM⟩ := coulomb_testFunction_c1_bound φ
  have hsq : ∀ z, ‖φ z ^ 2‖ ≤ M ^ 2 := fun z => by
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (φ z)) (hM z).1 2
  unfold conditionalEntropyBranchCoulombCoreLaw conditionalEntropyBranchDensityLaw
  apply (integrable_withDensity_iff (φ.continuous.measurable.pow_const 2).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using
    hB.mul_bdd (φ.continuous.measurable.pow_const 2).aestronglyMeasurable (Eventually.of_forall hsq)

theorem conditionalEntropyBranch_normalized_core_defective {N : ℕ} {β K : ℝ}
    (hN : 2 ≤ N + 1) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1)
    (hUpper : (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
      K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β)) :
    entropy (coulombMeasure (N + 1) β) (fun z => φ z ^ 2) ≤
      ((2 * K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
        ∂coulombMeasure (N + 1) β) + 2 * conditionalEntropyBranchUniformDefect R 2 : ℝ) : EReal) := by
  letI := coulombMeasure_isProbability (N := N + 1) hβ
  obtain ⟨hQ, hKL⟩ := conditionalEntropyBranchCoulombCoreLaw_finite_kl hβ φ hmass
  letI := hQ
  have hB := conditionalEntropyBranch_B_core_integrable (Nat.succ_pos N) hβ R φ
  have hl := conditionalEntropyBranch_uniform_factorization hN hβ R hKL hB (ell := 2) (by norm_num)
  rw [conditionalEntropyBranchCoulombS_eq_sum,
    ENNReal.toReal_sum (fun i _ => conditionalEntropyBranch_coulomb_site_finite hβ _ hKL i)] at hl
  have hr : (klDiv (conditionalEntropyBranchCoulombCoreLaw β φ) (coulombMeasure (N + 1) β)).toReal ≤
      2 * K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
        ∂coulombMeasure (N + 1) β) + 2 * conditionalEntropyBranchUniformDefect R 2 := by
    norm_num at hl
    nlinarith [hl, hUpper]
  obtain ⟨M, hMpos, hM⟩ := coulomb_testFunction_c1_bound φ
  have hi : Integrable (fun z => φ z ^ 2) (coulombMeasure (N + 1) β) :=
    Rothaus.integrable_continuous_comp_bounded φ.continuous.measurable
      (fun z => (hM z).1) (continuous_id.pow 2)
  rw [conditionalEntropyBranch_normalized_entropy_kl (φ.continuous.measurable.pow_const 2)
    (fun _ => sq_nonneg _) hi hmass]
  change (↑(klDiv (conditionalEntropyBranchCoulombCoreLaw β φ)
    (coulombMeasure (N + 1) β)) : EReal) ≤ _
  rw [← EReal.coe_ennreal_toReal hKL]
  exact EReal.coe_le_coe_iff.mpr hr

/-- A fixed one-site coefficient and an upper bound for the literal uniform
defect give the full original-form defective inequality. -/
theorem conditionalEntropyBranch_full_defective_of_core_upper {N : ℕ} {β K D : ℝ}
    (hN : 2 ≤ N + 1) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (hK : 0 < K) (hD : 0 ≤ D) (hDefect : conditionalEntropyBranchUniformDefect R 2 ≤ D)
    (hUpper : ∀ φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤,
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
      (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
        K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β))
    (u : CoulombFormDomain (N + 1) hβ) :
    entropy (coulombMeasure (N + 1) β) (fun z => (coulombFormValueL (N + 1) hβ u z) ^ 2) ≤
      ((2 * K * coulombFormEnergy (N + 1) hβ u +
        2 * D * (∫ z, (coulombFormValueL (N + 1) hβ u z) ^ 2 ∂coulombMeasure (N + 1) β) : ℝ) : EReal) := by
  refine conditionalEntropyBranch_form_of_core hβ (fun φ => ?_) u
  refine conditionalEntropyBranch_core_denormalize hβ (by positivity : 0 ≤ 2 * K)
    (mul_nonneg (by norm_num) hD) ?_ φ
  intro ψ hmass
  have h := conditionalEntropyBranch_normalized_core_defective hN hβ R ψ hmass (hUpper ψ hmass)
  apply h.trans
  apply EReal.coe_le_coe_iff.mpr
  linarith [hDefect]

/-- The literal full-domain defective coefficient 4/rho_one and 2D, with
rho_one defined from the same K used in the full one-site/core joint witness. -/
theorem conditionalEntropyBranch_full_defective {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    ∃ K rhoOne : ℝ, 0 < K ∧ rhoOne = 2 / K ∧ 0 < rhoOne ∧
      (∀ (N : ℕ) (y : CoulombConfig N),
        ∀ u : PointFormDomain hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j),
        entropy (coulombOneSiteKernel N β hβ y)
          (fun w => (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w) ^ 2) ≤
          (((2 / rhoOne) * pointFormEnergy hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u : ℝ) : EReal)) ∧
      ∀ (N : ℕ), 2 ≤ N + 1 → ∀ u : CoulombFormDomain (N + 1) hβ,
        entropy (coulombMeasure (N + 1) β) (fun z => (coulombFormValueL (N + 1) hβ u z) ^ 2) ≤
          (((4 / rhoOne) * coulombFormEnergy (N + 1) hβ u +
            2 * conditionalEntropyBranchUniformDefect R 2 *
              (∫ z, (coulombFormValueL (N + 1) hβ u z) ^ 2 ∂coulombMeasure (N + 1) β) : ℝ) : EReal) := by
  obtain ⟨K, hK, hFull, hCore⟩ := conditionalEntropyBranch_joint_one_site_constant hβ
  obtain ⟨hrho, htwo, hfour⟩ := conditionalEntropyBranch_one_site_rate_normalization hK
  refine ⟨K, 2 / K, hK, rfl, hrho, ?_, ?_⟩
  · simpa only [htwo] using hFull
  · intro N hN u
    rw [hfour]
    exact conditionalEntropyBranch_full_defective_of_core_upper hN hβ R hK
      (conditionalEntropyBranch_uniform_defect_nonneg hβ (by norm_num : (1 : ℝ) < 2) R) le_rfl
      (fun φ hmass => (hCore N φ hmass).2) u

end RepulsiveCoulomb
