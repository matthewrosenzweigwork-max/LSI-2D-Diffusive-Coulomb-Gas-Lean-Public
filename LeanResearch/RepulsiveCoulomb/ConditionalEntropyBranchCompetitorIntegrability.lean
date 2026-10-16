module

public import LeanResearch.RepulsiveCoulomb.CoulombFiniteEntropyMoment
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceBounds
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedDefinition
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchFiniteIntegrability

@[expose] public section

/-!
Actual competitor integrability needed before the thermal product entropy
expansion. Finite KL against the physical Gibbs law supplies quadratic moment;
the constructed thermal potential bounds then supply every U term. The stated
B-integrability hypothesis yields A-integrability, and a signed finite-sum
argument proves each off-diagonal logarithmic pair term integrable.
The constructed-reference and finite-entropy-moment dependencies are explicit
records-only future inputs; they are not claimed checked here.
-/
noncomputable section
open MeasureTheory InformationTheory Real Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

def conditionalEntropyBranchThermalB {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (z : CoulombConfig N) : ℝ :=
  equilibriumModulatedEnergy R.density (WithLp.ofLp z) +
    (∑ i, equilibriumDensityPotential R.density (z i)) / (N : ℝ)

theorem conditionalEntropyBranch_log_coordinate_integrable {N : ℕ}
    {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hQ2 : Integrable (fun z : CoulombConfig N => ‖z‖ ^ 2) Q) (i : Fin N) :
    Integrable (fun z => equilibriumLogMoment (z i)) Q := by
  apply (hQ2.add (integrable_const 1)).mono'
    ((equilibriumLogMoment_continuous.comp (coulombCoordinate i).continuous).aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  change ‖equilibriumLogMoment (z i)‖ ≤ ‖z‖ ^ 2 + 1
  rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumLogMoment_nonneg _)]
  have hcoord := PiLp.norm_apply_le z i
  have hnorm : ‖z‖ ≤ ‖z‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  exact (equilibriumLogMoment_le_norm (z i)).trans (hcoord.trans hnorm)

theorem conditionalEntropyBranch_thermal_coordinate_integrable {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hQ2 : Integrable (fun z : CoulombConfig N => ‖z‖ ^ 2) Q) (i : Fin N) :
    Integrable (fun z => equilibriumDensityPotential R.density (z i)) Q := by
  have hm := (equilibriumDensityPotential_measurable R.smooth.continuous.measurable).comp
    (coulombCoordinate i).continuous.measurable
  apply integrable_of_le_of_le hm.aestronglyMeasurable
    (g₁ := fun z => -equilibriumLogMoment (z i) -
      ∫ y : ℂ, equilibriumLogMoment y * R.density y) (g₂ := fun _ => (1 / 2 : ℝ))
  · exact Eventually.of_forall (fun z => equilibriumReference_potential_lower R (z i))
  · exact Eventually.of_forall (fun z => equilibriumReference_potential_upper R (z i))
  · exact (conditionalEntropyBranch_log_coordinate_integrable hQ2 i).neg.sub (integrable_const _)
  · exact integrable_const _

theorem conditionalEntropyBranch_thermal_sum_integrable {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hQ2 : Integrable (fun z : CoulombConfig N => ‖z‖ ^ 2) Q) :
    Integrable (fun z => ∑ i, equilibriumDensityPotential R.density (z i)) Q :=
  integrable_finsetSum Finset.univ
    (fun i _ => conditionalEntropyBranch_thermal_coordinate_integrable R hQ2 i)

/-- The manuscript's B hypothesis is used exactly as stated; A and all U
terms are proved integrable, not added as new assumptions. -/
theorem conditionalEntropyBranch_finite_entropy_A_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure N β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) :
    (∀ i : Fin N, Integrable (fun z => equilibriumDensityPotential R.density (z i)) Q) ∧
      Integrable (fun z => equilibriumModulatedEnergy R.density (WithLp.ofLp z)) Q := by
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ hKL).1
  have hU := conditionalEntropyBranch_thermal_sum_integrable R hQ2
  refine ⟨fun i => conditionalEntropyBranch_thermal_coordinate_integrable R hQ2 i, ?_⟩
  have h : Integrable (fun z => conditionalEntropyBranchThermalB R z -
      (∑ i, equilibriumDensityPotential R.density (z i)) / (N : ℝ)) Q :=
    hB.sub (hU.div_const (N : ℝ))
  simpa only [conditionalEntropyBranchThermalB, Pi.sub_apply, add_sub_cancel_right] using h

/-- Integrability of the ordered sum is proved before extracting individual
singular pair terms. This uses no positivity by cancellation. -/
theorem conditionalEntropyBranch_ordered_log_integrable {N : ℕ} {β : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure N β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) :
    Integrable (fun z : CoulombConfig N => equilibriumOrderedOffDiagonalSum
      (fun i j => equilibriumLogKernel (z i - z j))) Q := by
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ hKL).1
  have hU := conditionalEntropyBranch_thermal_sum_integrable R hQ2
  have hA := (conditionalEntropyBranch_finite_entropy_A_integrable hβ R hKL hB).2
  have h := ((hA.add hU).sub
    (integrable_const ((N : ℝ) * equilibriumDensityInteraction R.density / 2))).const_mul (2 * (N : ℝ))
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert h using 1
  funext z
  dsimp only [equilibriumModulatedEnergy, Pi.add_apply, Pi.sub_apply]
  field_simp [hn] <;> ring

/-- Each actual pair logarithm is integrable for every finite-KL competitor
under the proposition's original B-integrability hypothesis. The lower bound
controls its negative tail, so no infinity-minus-infinity reasoning is used. -/
theorem conditionalEntropyBranch_pair_log_integrable {N : ℕ} {β : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure N β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q)
    (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun z => equilibriumLogKernel (z i - z j)) Q := by
  classical
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ hKL).1
  let f : (Fin N × Fin N) → CoulombConfig N → ℝ := fun p z =>
    if p.1 = p.2 then 0 else equilibriumLogKernel (z p.1 - z p.2)
  let g : (Fin N × Fin N) → CoulombConfig N → ℝ := fun p z =>
    -equilibriumLogMoment (z p.1) - equilibriumLogMoment (z p.2)
  have hfm (p : Fin N × Fin N) : AEStronglyMeasurable (f p) Q := by
    dsimp only [f]
    split_ifs
    · exact stronglyMeasurable_const.aestronglyMeasurable
    · exact (equilibriumLogKernel_measurable.comp
        ((coulombCoordinate p.1).continuous.measurable.sub
          (coulombCoordinate p.2).continuous.measurable)).aestronglyMeasurable
  have hgi (p : Fin N × Fin N) : Integrable (g p) Q :=
    (conditionalEntropyBranch_log_coordinate_integrable hQ2 p.1).neg.sub
      (conditionalEntropyBranch_log_coordinate_integrable hQ2 p.2)
  have hlower (p : Fin N × Fin N) (z : CoulombConfig N) : g p z ≤ f p z := by
    dsimp only [g, f]
    split_ifs
    · linarith [equilibriumLogMoment_nonneg (z p.1), equilibriumLogMoment_nonneg (z p.2)]
    · exact equilibriumLogKernel_sub_lower _ _
  have hsum : Integrable (fun z => ∑ p, f p z) Q := by
    simpa only [f, Fintype.sum_prod_type, equilibriumOrderedOffDiagonalSum] using
      conditionalEntropyBranch_ordered_log_integrable hN hβ R hKL hB
  have h := conditionalEntropyBranch_integrable_of_finite_sum Q hfm hgi hlower hsum (i, j)
  simpa only [f, hij, if_false] using h

end RepulsiveCoulomb
