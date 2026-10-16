module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchThermalTilt
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchChartCompatibility
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchOrderedCounting
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedDefinition

@[expose] public section

/-!
Actual thermal-reference conditional means and exact ordered-pair centering.
Kernel/potential integrability is proved before signed integration. This is
the literal 2 A_N + N^{-1} sum U term, including the surviving c normalization.
Records-only draft with explicit uncompiled thermal-reference dependencies.
-/
noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_reference_kernel_integrable {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : ℂ) :
    Integrable (fun w => equilibriumLogKernel (w - y)) (R.measure : Measure ℂ) := by
  rw [← R.density_measure]
  apply (equilibriumDensityMeasure_integrable_iff R.smooth.continuous.measurable
    (fun w => (R.positive w).le) _).mpr
  simpa only [equilibriumLogKernel, norm_sub_rev] using
    equilibriumLogKernel_mul_integrable R.smooth.continuous.measurable
      (fun w => (R.positive w).le) R.cap R.integrable
      (equilibriumReference_logMoment_integrable R) y

theorem conditionalEntropyBranch_reference_kernel_mean {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : ℂ) :
    (∫ w, equilibriumLogKernel (w - y) ∂(R.measure : Measure ℂ)) =
      equilibriumDensityPotential R.density y := by
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun w => (R.positive w).le)]
  unfold equilibriumDensityPotential
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => by simp only [equilibriumLogKernel, norm_sub_rev, mul_comm])

theorem conditionalEntropyBranch_reference_U_integrable {β : ℝ}
    (R : EquilibriumConstructedReference β) :
    Integrable (equilibriumDensityPotential R.density) (R.measure : Measure ℂ) := by
  rw [← R.density_measure]
  exact (equilibriumDensityMeasure_integrable_iff R.smooth.continuous.measurable
    (fun w => (R.positive w).le) _).mpr
      (equilibriumDensityInteraction_integrable R.smooth.continuous.measurable
        (fun w => (R.positive w).le) R.cap R.integrable R.mass_one
        (equilibriumReference_logMoment_integrable R))

theorem conditionalEntropyBranch_reference_U_mean {β : ℝ}
    (R : EquilibriumConstructedReference β) :
    (∫ w, equilibriumDensityPotential R.density w ∂(R.measure : Measure ℂ)) =
      equilibriumDensityInteraction R.density := by
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun w => (R.positive w).le)]
  unfold equilibriumDensityInteraction
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => mul_comm _ _)

theorem conditionalEntropyBranch_reference_phi_integrable {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    Integrable (conditionalEntropyBranchThermalPhi R y) (R.measure : Measure ℂ) :=
  ((integrable_finsetSum Finset.univ (fun j _ =>
    conditionalEntropyBranch_reference_kernel_integrable R (y j))).div_const _).sub
      (conditionalEntropyBranch_reference_U_integrable R)

theorem conditionalEntropyBranch_reference_phi_mean {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    (∫ w, conditionalEntropyBranchThermalPhi R y w ∂(R.measure : Measure ℂ)) =
      (∑ j, equilibriumDensityPotential R.density (y j)) / ((N + 1 : ℕ) : ℝ) -
        equilibriumDensityInteraction R.density := by
  unfold conditionalEntropyBranchThermalPhi
  rw [integral_sub ((integrable_finsetSum Finset.univ (fun j _ =>
    conditionalEntropyBranch_reference_kernel_integrable R (y j))).div_const _)
      (conditionalEntropyBranch_reference_U_integrable R), integral_div,
    integral_finsetSum Finset.univ (fun j _ => conditionalEntropyBranch_reference_kernel_integrable R (y j)),
    conditionalEntropyBranch_reference_U_mean]
  simp_rw [conditionalEntropyBranch_reference_kernel_mean]

theorem conditionalEntropyBranch_sum_swap_outside {N : ℕ} (i : Fin (N + 1))
    (h : Fin (N + 1) → ℝ) :
    (∑ j : Fin N, h (Equiv.swap 0 i j.succ)) =
      ∑ j : Fin (N + 1), if i = j then 0 else h j := by
  rw [conditionalEntropyBranch_offDiagonal_row]
  have he := Equiv.sum_comp (Equiv.swap (0 : Fin (N + 1)) i) h
  rw [Fin.sum_univ_succ, Equiv.swap_apply_left] at he
  linarith

theorem conditionalEntropyBranch_thermal_phi_at_site {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (z : CoulombConfig (N + 1)) (i : Fin (N + 1)) :
    conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1
        (conditionalEntropyBranchCoulombChart i z).2 =
      (∑ j, if i = j then 0 else equilibriumLogKernel (z i - z j)) / ((N + 1 : ℕ) : ℝ) -
        equilibriumDensityPotential R.density (z i) := by
  unfold conditionalEntropyBranchThermalPhi
  simp_rw [conditionalEntropyBranchCoulombChart_site, conditionalEntropyBranchCoulombChart_outside]
  exact congrArg (fun t : ℝ => t / ((N + 1 : ℕ) : ℝ) -
    equilibriumDensityPotential R.density (z i))
      (conditionalEntropyBranch_sum_swap_outside i
        (fun j => equilibriumLogKernel (z i - z j)))

/-- Literal manuscript ordered-pair equality in the physical conditioning
charts. Physical density equalities remain the separate a.e. tilt theorem. -/
theorem conditionalEntropyBranch_thermal_centered_sum {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (z : CoulombConfig (N + 1)) :
    (∑ i : Fin (N + 1),
      (conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1
        (conditionalEntropyBranchCoulombChart i z).2 -
        ∫ w, conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1 w
          ∂(R.measure : Measure ℂ))) =
      2 * equilibriumModulatedEnergy R.density (WithLp.ofLp z) +
        (∑ i, equilibriumDensityPotential R.density (z i)) / ((N + 1 : ℕ) : ℝ) := by
  have hOutside (i : Fin (N + 1)) :
      (∑ j : Fin N, equilibriumDensityPotential R.density (z (Equiv.swap 0 i j.succ))) =
        ∑ j : Fin (N + 1), if i = j then 0 else equilibriumDensityPotential R.density (z j) :=
    conditionalEntropyBranch_sum_swap_outside i
      (fun j => equilibriumDensityPotential R.density (z j))
  simp_rw [conditionalEntropyBranch_thermal_phi_at_site,
    conditionalEntropyBranch_reference_phi_mean, conditionalEntropyBranchCoulombChart_outside,
    hOutside]
  exact conditionalEntropyBranch_ordered_pair_identity (Nat.succ_pos N)
    (fun i j => equilibriumLogKernel (z i - z j))
    (fun i => equilibriumDensityPotential R.density (z i)) (equilibriumDensityInteraction R.density)

end RepulsiveCoulomb
