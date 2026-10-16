import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCompetitorIntegrability
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchThermalCounting
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchConditionalMean
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombKL

/-!
Integrability interfaces for every actual selected-label conditional under
the manuscript finite-Gibbs-KL and B-integrability hypotheses. In particular,
the conditional log normalizer is proved integrable from its point-weight
bound and the competitor moment, before any entropy expansion is integrated.
Records-only draft with explicit uncompiled dependencies.
-/
noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_phi_comp_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) (i : Fin (N + 1)) :
    Integrable (fun z => conditionalEntropyBranchThermalPhi R
      (conditionalEntropyBranchCoulombChart i z).1 (conditionalEntropyBranchCoulombChart i z).2) Q := by
  have hrow (j : Fin (N + 1)) : Integrable
      (fun z => if i = j then 0 else equilibriumLogKernel (z i - z j)) Q := by
    by_cases hij : i = j
    · simp only [hij, if_true]
      exact integrable_zero _ _ _
    · simpa only [hij, if_false] using conditionalEntropyBranch_pair_log_integrable
        (Nat.succ_pos N) hβ R hKL hB i j hij
  have hU := (conditionalEntropyBranch_finite_entropy_A_integrable hβ R hKL hB).1 i
  simp_rw [conditionalEntropyBranch_thermal_phi_at_site]
  exact ((integrable_finsetSum Finset.univ (fun j _ => hrow j)).div_const _).sub hU

theorem conditionalEntropyBranch_phi_joint_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) (i : Fin (N + 1)) :
    Integrable (fun p : CoulombConfig N × ℂ => conditionalEntropyBranchThermalPhi R p.1 p.2)
      (Q.map (conditionalEntropyBranchCoulombChart i)) :=
  (integrable_map_measure (conditionalEntropyBranchThermalPhi_measurable R).aestronglyMeasurable
    (conditionalEntropyBranchCoulombChart i).measurable.aemeasurable).mpr
      (conditionalEntropyBranch_phi_comp_integrable hβ R hKL hB i)

theorem conditionalEntropyBranch_outside_log_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞) (i : Fin (N + 1)) (j : Fin N) :
    Integrable (fun y : CoulombConfig N => equilibriumLogMoment (y j))
      (Q.map (conditionalEntropyBranchCoulombChart i)).fst := by
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ hKL).1
  rw [Measure.fst, Measure.map_map measurable_fst (conditionalEntropyBranchCoulombChart i).measurable]
  apply (integrable_map_measure
    ((equilibriumLogMoment_continuous.comp (coulombCoordinate j).continuous).aestronglyMeasurable)
      (measurable_fst.comp (conditionalEntropyBranchCoulombChart i).measurable).aemeasurable).mpr
  change Integrable (fun z =>
    equilibriumLogMoment ((conditionalEntropyBranchCoulombChart i z).1 j)) Q
  simpa only [conditionalEntropyBranchCoulombChart_outside] using
    conditionalEntropyBranch_log_coordinate_integrable hQ2 (Equiv.swap 0 i j.succ)

theorem conditionalEntropyBranch_log_normalizer_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞) (i : Fin (N + 1)) :
    Integrable (fun y : CoulombConfig N => Real.log
      (∫ w, Real.exp (-β * conditionalEntropyBranchThermalPhi R y w) ∂(R.measure : Measure ℂ)))
      (Q.map (conditionalEntropyBranchCoulombChart i)).fst := by
  have h := conditionalEntropyBranch_point_log_normalizer_integrable hβ hβ.le
    (coulombOneSiteExponents_nonneg N hβ.le) (coulomb_one_site_exponent_sum_lt N hβ).le
    (Q.map (conditionalEntropyBranchCoulombChart i)).fst
    (fun j => conditionalEntropyBranch_outside_log_integrable hβ hKL i j)
  simp_rw [conditionalEntropyBranch_thermal_log_normalizer hβ R]
  exact (integrable_const _).add h

theorem conditionalEntropyBranch_reference_mean_comp_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) (i : Fin (N + 1)) :
    Integrable (fun z => ∫ w, conditionalEntropyBranchThermalPhi R
      (conditionalEntropyBranchCoulombChart i z).1 w ∂(R.measure : Measure ℂ)) Q := by
  have hU := (conditionalEntropyBranch_finite_entropy_A_integrable hβ R hKL hB).1
  simp_rw [conditionalEntropyBranch_reference_phi_mean, conditionalEntropyBranchCoulombChart_outside]
  exact ((integrable_finsetSum Finset.univ (fun j _ => hU (Equiv.swap 0 i j.succ))).div_const _).sub
    (integrable_const _)

theorem conditionalEntropyBranch_reference_mean_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) (i : Fin (N + 1)) :
    Integrable (fun y : CoulombConfig N => ∫ w, conditionalEntropyBranchThermalPhi R y w
      ∂(R.measure : Measure ℂ)) (Q.map (conditionalEntropyBranchCoulombChart i)).fst := by
  have hm : Measurable (fun y : CoulombConfig N => ∫ w, conditionalEntropyBranchThermalPhi R y w
      ∂(R.measure : Measure ℂ)) :=
    (conditionalEntropyBranchThermalPhi_measurable R).stronglyMeasurable.integral_prod_right'.measurable
  rw [Measure.fst, Measure.map_map measurable_fst (conditionalEntropyBranchCoulombChart i).measurable]
  exact (integrable_map_measure hm.aestronglyMeasurable
    (measurable_fst.comp (conditionalEntropyBranchCoulombChart i).measurable).aemeasurable).mpr
      (conditionalEntropyBranch_reference_mean_comp_integrable hβ R hKL hB i)

end RepulsiveCoulomb
