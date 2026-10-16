module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.PaperOneSiteEntropy
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchDefectiveLSI

@[expose] public section

/-! Additive experimental source; verification is recorded separately in evidence. The supplied thermal reference is
physical data, not an old selected constructor. Uniform inputs are literal
partition and Gibbs exponential-moment bounds, not a factorization or LSI
certificate. Those inputs await the source-aligned thermal/DG/Holder chain.
The actual finite defect is bounded before the real supremum is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory InformationTheory Real Filter
open PeriodicAttractiveLogGas
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- The physical Gibbs exponential moment at the manuscript choice ell=2. -/
def paperGibbsEntropyMoment {β : ℝ} (R : EquilibriumConstructedReference β) (N : ℕ) : ℝ :=
  ∫ z : CoulombConfig N, Real.exp (-2 * β * conditionalEntropyBranchThermalB R z)
    ∂coulombMeasure N β

/-- The literal all-particle defect supremum. Boundedness must be supplied
by the actual physical moment estimates before applying any supremum lemma. -/
def paperUniformEntropyDefect {β : ℝ} (R : EquilibriumConstructedReference β) : ℝ :=
  sSup (Set.range (fun n : ℕ => conditionalEntropyBranchDefect (N := n + 2) R 2))

theorem paper_finite_defect_le_of_integral_bounds {β C M : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (hK : equilibriumReferencePartition N β R ≤ C)
    (hM : paperGibbsEntropyMoment R N ≤ M) :
    conditionalEntropyBranchDefect (N := N) R 2 ≤ max 0 (Real.log C + Real.log M / 2) := by
  let := coulombMeasure_isProbability (N := N) hβ
  have hKP := equilibriumReferencePartition_canonical_pos hβ R N
  have hMP : 0 < paperGibbsEntropyMoment R N :=
    integral_exp_pos (conditionalEntropyBranch_defect_exp_integrable hN hβ (by norm_num) R)
  have hk := Real.log_le_log hKP hK
  have hm := Real.log_le_log hMP hM
  unfold conditionalEntropyBranchDefect
  change Real.log (equilibriumReferencePartition N β R) + Real.log (paperGibbsEntropyMoment R N) / 2 ≤ _
  exact (add_le_add hk (div_le_div_of_nonneg_right hm (by norm_num))).trans (le_max_right _ _)

theorem paper_defect_range_bddAbove {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M) :
    BddAbove (Set.range (fun n : ℕ => conditionalEntropyBranchDefect (N := n + 2) R 2)) := by
  refine ⟨max 0 (Real.log C + Real.log M / 2), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact paper_finite_defect_le_of_integral_bounds hβ R (by omega) (hK (n + 2) (by omega))
    (hM (n + 2) (by omega))

theorem paper_defect_le_uniform {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M)
    {N : ℕ} (hN : 2 ≤ N) :
    conditionalEntropyBranchDefect (N := N) R 2 ≤ paperUniformEntropyDefect R := by
  apply le_csSup (paper_defect_range_bddAbove hβ R hK hM)
  refine ⟨N - 2, ?_⟩
  change conditionalEntropyBranchDefect (N := N - 2 + 2) R 2 =
    conditionalEntropyBranchDefect (N := N) R 2
  rw [Nat.sub_add_cancel hN]

theorem paper_uniform_defect_nonneg {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M) :
    0 ≤ paperUniformEntropyDefect R :=
  (conditionalEntropyBranch_defect_nonneg (N := 2) (by norm_num) hβ (by norm_num) R).trans
    (paper_defect_le_uniform hβ R hK hM (N := 2) le_rfl)

theorem paper_uniform_defect_le {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M) :
    paperUniformEntropyDefect R ≤ max 0 (Real.log C + Real.log M / 2) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact paper_finite_defect_le_of_integral_bounds hβ R (by omega) (hK (n + 2) (by omega))
    (hM (n + 2) (by omega))

theorem paper_normalized_core_defective {N : ℕ} {β K : ℝ}
    (_hN : 2 ≤ N + 1) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤)
    (hmass : (∫ z, φ z ^ 2 ∂coulombMeasure (N + 1) β) = 1)
    (hUpper : (∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ
        (conditionalEntropyBranchCoulombCoreLaw β φ) i).toReal) ≤
      K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 1) β)) :
    entropy (coulombMeasure (N + 1) β) (fun z => φ z ^ 2) ≤
      ((2 * K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
        ∂coulombMeasure (N + 1) β) + 2 * conditionalEntropyBranchDefect (N := N + 1) R 2 : ℝ) : EReal) := by
  let := coulombMeasure_isProbability (N := N + 1) hβ
  obtain ⟨hQ, hKL⟩ := conditionalEntropyBranchCoulombCoreLaw_finite_kl hβ φ hmass
  let := hQ
  have hB := conditionalEntropyBranch_B_core_integrable (Nat.succ_pos N) hβ R φ
  have hl := conditionalEntropyBranch_factorization_defect_of_exp_integrable hβ R hKL hB
    (ell := 2) (by norm_num)
    (conditionalEntropyBranch_defect_exp_integrable (Nat.succ_pos N) hβ (by norm_num) R)
  rw [conditionalEntropyBranchCoulombS_eq_sum,
    ENNReal.toReal_sum (fun i _ => conditionalEntropyBranch_coulomb_site_finite hβ _ hKL i)] at hl
  have hr : (klDiv (conditionalEntropyBranchCoulombCoreLaw β φ) (coulombMeasure (N + 1) β)).toReal ≤
      2 * K * (∫ z, ‖gradient (φ : CoulombConfig (N + 1) → ℝ) z‖ ^ 2
        ∂coulombMeasure (N + 1) β) + 2 * conditionalEntropyBranchDefect (N := N + 1) R 2 := by
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

/-- Conditional only on physical thermal data and actual uniform integral
bounds. No old reference, old uniform-defect witness, or old one-site rate is
selected. New thermal/DG producers must discharge the displayed inputs. -/
theorem paper_full_defective_of_reference_bounds {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((4 / paperOneSiteRate β) * coulombFormEnergy N hβ u +
        2 * paperUniformEntropyDefect R *
          (∫ z, (coulombFormValueL N hβ u z) ^ 2 ∂coulombMeasure N β) : ℝ) : EReal) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hD := paper_uniform_defect_nonneg hβ R hK hM
  refine conditionalEntropyBranch_form_of_core hβ (fun φ => ?_) u
  refine conditionalEntropyBranch_core_denormalize hβ
    (div_pos (by norm_num) (paperOneSiteRate_pos hβ)).le
    (mul_nonneg (by norm_num) hD) ?_ φ
  intro ψ hmass
  have h := paper_normalized_core_defective (N := n + 1) (K := 2 / paperOneSiteRate β)
    (by omega) hβ R ψ hmass (paper_core_one_site_sum hβ (n + 1) ψ hmass)
  have hd := paper_defect_le_uniform hβ R hK hM (N := n + 2) (by omega)
  apply h.trans
  apply EReal.coe_le_coe_iff.mpr
  have hcoef : 2 * (2 / paperOneSiteRate β) = 4 / paperOneSiteRate β := by ring
  rw [hcoef]
  linarith

end RepulsiveCoulomb.PaperRoute
