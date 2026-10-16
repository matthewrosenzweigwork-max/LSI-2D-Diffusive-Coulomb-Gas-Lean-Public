module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchWeightedCost
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchTransport
public import LeanResearch.RepulsiveCoulomb.CoulombCoreConditional
public import LeanResearch.RepulsiveCoulomb.CoulombOneSiteJointLaw
public import LeanResearch.RepulsiveCoulomb.CoulombCutoffEnergy

@[expose] public section

/-!
Actual first-coordinate conditional KL of Q = phi^2 P for the unchanged
collision-free Coulomb core. The integrated upper bound uses the checked
one-site LSI and the exact physical coordinate of the full Euclidean gradient.
Neither an abstract conditional factorization nor a different form domain is
substituted. All-label summation remains a separate permutation-transport step.
Records-only draft, not staged or checked.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory Filter
open PeriodicAttractiveLogGas
open scoped ENNReal
namespace RepulsiveCoulomb

def conditionalEntropyBranchCoulombCoreLaw {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : Measure (CoulombConfig N) :=
  conditionalEntropyBranchDensityLaw (coulombMeasure N β) (fun z => φ z ^ 2)

def conditionalEntropyBranchCoulombFirstCost {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤) : ℝ≥0∞ :=
  klDiv ((conditionalEntropyBranchCoulombCoreLaw β φ).map (coulombFrozenFirst N))
    (((conditionalEntropyBranchCoulombCoreLaw β φ).map (coulombFrozenFirst N)).fst ⊗ₘ
      coulombOneSiteKernel N β hβ)

theorem conditionalEntropyBranchCoulombCoreLaw_finite_kl {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure N β) = 1) :
    IsProbabilityMeasure (conditionalEntropyBranchCoulombCoreLaw β φ) ∧
      klDiv (conditionalEntropyBranchCoulombCoreLaw β φ) (coulombMeasure N β) ≠ ∞ := by
  letI := coulombMeasure_isProbability (N := N) hβ
  obtain ⟨B, hBpos, hB⟩ := coulomb_testFunction_c1_bound φ
  have hi : Integrable (fun z => φ z ^ 2) (coulombMeasure N β) :=
    Rothaus.integrable_continuous_comp_bounded φ.continuous.measurable
      (fun z => (hB z).1) (continuous_id.pow 2)
  have hl : Integrable (fun z => φ z ^ 2 * Real.log (φ z ^ 2)) (coulombMeasure N β) :=
    Rothaus.integrable_continuous_comp_bounded φ.continuous.measurable
      (fun z => (hB z).1) (Real.continuous_mul_log.comp (continuous_id.pow 2))
  exact ⟨conditionalEntropyBranchDensityLaw_probability (fun z => sq_nonneg _) hi hmass,
    conditionalEntropyBranch_density_kl_finite (φ.continuous.measurable.pow_const 2)
      (fun z => sq_nonneg _) hi hmass hl⟩

/-- The genuinely integrated first-site entropy estimate for the actual
normalized density phi^2 P. K is the checked one-site entropy coefficient,
equivalently 2/rho_one, and is independent of N and the frozen configuration. -/
theorem conditionalEntropyBranch_coulomb_first_core_upper_of_conditional {β : ℝ}
    (hβ : 0 < β) (K : ℝ)
    (hOne : ∀ (N : ℕ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      entropy (coulombOneSiteKernel N β hβ y) (fun w => φ (coulombInsertZero w y) ^ 2) ≤
        ((K * (∫ w, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2
          ∂coulombOneSiteKernel N β hβ y) : ℝ) : EReal)) :
    ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
      conditionalEntropyBranchCoulombFirstCost hβ φ ≠ ∞ ∧
        (conditionalEntropyBranchCoulombFirstCost hβ φ).toReal ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z 0‖ ^ 2
            ∂coulombMeasure (N + 1) β) := by
  intro N φ hmass
  letI := coulombMeasure_isProbability (N := N + 1) hβ
  letI := coulombOneSiteMarginal_isProbability (N := N) hβ
  let μ := coulombOneSiteMarginal N β
  let κ := coulombOneSiteKernel N β hβ
  let F : CoulombConfig N × ℂ → ℝ := fun p => φ ((coulombFrozenFirst N).symm p) ^ 2
  let E : CoulombConfig N → ℝ := fun y => ∫ w,
    ‖gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0‖ ^ 2 ∂κ y
  obtain ⟨B, hBpos, hB⟩ := coulomb_testFunction_c1_bound φ
  have hFm : Measurable F :=
    (φ.continuous.measurable.comp (coulombFrozenFirst N).symm.measurable).pow_const 2
  have hF0 : ∀ p, 0 ≤ F p := fun _ => sq_nonneg _
  have hFi (y : CoulombConfig N) : Integrable (fun w => F (y, w)) (κ y) := by
    exact Rothaus.integrable_continuous_comp_bounded
      (φ.continuous.measurable.comp ((coulombFrozenFirst N).symm.measurable.comp measurable_prodMk_left))
      (fun w => (hB ((coulombFrozenFirst N).symm (y, w))).1) (continuous_id.pow 2)
  have hFl (y : CoulombConfig N) :
      Integrable (fun w => F (y, w) * Real.log (F (y, w))) (κ y) := by
    exact Rothaus.integrable_continuous_comp_bounded
      (φ.continuous.measurable.comp ((coulombFrozenFirst N).symm.measurable.comp measurable_prodMk_left))
      (fun w => (hB ((coulombFrozenFirst N).symm (y, w))).1)
      (Real.continuous_mul_log.comp (continuous_id.pow 2))
  have hOrig : Integrable (fun z => φ z ^ 2) (coulombMeasure (N + 1) β) :=
    Rothaus.integrable_continuous_comp_bounded φ.continuous.measurable
      (fun z => (hB z).1) (continuous_id.pow 2)
  have hF : Integrable F (μ ⊗ₘ κ) :=
    (coulombFrozenFirst_measurePreserving (N := N) hβ).symm.integrable_comp_of_integrable hOrig
  have hmassF : (∫ p, F p ∂μ ⊗ₘ κ) = 1 := by
    exact ((coulombFrozenFirst_measurePreserving (N := N) hβ).symm.integral_comp'
      (fun z => φ z ^ 2)).trans hmass
  have hg : MemLp (fun z => gradient (φ : CoulombConfig (N + 1) → ℝ) z) 2
      (coulombMeasure (N + 1) β) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  have hG : Integrable (fun z => ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z 0‖ ^ 2)
      (coulombMeasure (N + 1) β) :=
    (hg.continuousLinearMap_comp (coulombCoordinate 0)).norm.integrable_sq
  have hE : Integrable E μ := by
    simpa only [E, κ, μ, abs_sq] using (coulomb_one_site_slice_integrability hβ hG).2
  have hbound (y : CoulombConfig N) : entropy (κ y) (fun w => F (y, w)) ≤
      ((K * E y : ℝ) : EReal) := by
    simpa only [F, E, κ, coulombFrozenFirst_symm_apply] using hOne N y φ
  have hcost := conditionalEntropyBranch_integrated_cost_upper μ κ hFm hF0 hFi hFl
    hF hmassF hE K hbound
  have hQ : (conditionalEntropyBranchCoulombCoreLaw β φ).map (coulombFrozenFirst N) =
      conditionalEntropyBranchDensityLaw (μ ⊗ₘ κ) F := by
    rw [conditionalEntropyBranchCoulombCoreLaw,
      conditionalEntropyBranch_densityLaw_map _ _ (φ.continuous.measurable.pow_const 2),
      coulomb_one_site_joint_law hβ]
  have hMarg := conditionalEntropyBranch_density_marginal μ κ hFm hF0 hFi hF hmassF
  have hEnergy : (∫ y, E y ∂μ) =
      ∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z 0‖ ^ 2 ∂coulombMeasure (N + 1) β :=
    (coulomb_one_site_integral_tower hβ hG).symm
  rw [hEnergy] at hcost
  simpa only [conditionalEntropyBranchCoulombFirstCost, hQ, hMarg] using hcost

/-- Existence wrapper retaining the checked core coefficient. The parameterized
version above is also available for one fixed full-domain one-site rate. -/
theorem conditionalEntropyBranch_coulomb_first_core_upper {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ)
      (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤),
      (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1 →
      conditionalEntropyBranchCoulombFirstCost hβ φ ≠ ∞ ∧
        (conditionalEntropyBranchCoulombFirstCost hβ φ).toReal ≤
          K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z 0‖ ^ 2
            ∂coulombMeasure (N + 1) β) := by
  obtain ⟨P, K, hP, hK, hOne⟩ := coulomb_core_one_site_inequalities hβ
  exact ⟨K, hK, conditionalEntropyBranch_coulomb_first_core_upper_of_conditional hβ K
    (fun N y φ => (hOne N y φ).2)⟩

end RepulsiveCoulomb
