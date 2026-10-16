import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedDefinition
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircleEmpiricalRepulsivity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircularPotential
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedCentering

/-! The actual deterministic Onsager lower bound for the canonical modulated
energy. Circular empirical self-energy is genuinely doubly smeared, the
reference is the actual thermal measure, and the sharp cross-error constant
is retained. Singular pointwise comparisons explicitly require injective
particle positions. No all-configurations claim is made from i!=j alone. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

theorem equilibriumFullSum_eq_offDiagonal_add_diagonal {N : ℕ} (H : Fin N → Fin N → ℝ) :
    (∑ i, ∑ j, H i j) = equilibriumOrderedOffDiagonalSum H + ∑ i, H i i := by
  classical
  have he (i j : Fin N) : H i j =
      (if i = j then 0 else H i j) + (if i = j then H i i else 0) := by
    split_ifs with h
    · subst j
      simp
    · simp
  calc
    (∑ i, ∑ j, H i j) =
        ∑ i, ∑ j, ((if i = j then 0 else H i j) + (if i = j then H i i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact he i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl

/-- The diagonal term is exactly -N log epsilon; the off-diagonal comparison
uses spatial collision-freeness, not merely distinct particle labels. -/
theorem equilibriumDoubleCircular_sum_le {N : ℕ} (z : Fin N → ℂ)
    (hz : Function.Injective z) {ε : ℝ} (hε : 0 < ε) :
    (∑ i : Fin N, ∑ j : Fin N, equilibriumDoubleCircularKernel ε (z i) (z j)) ≤
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) -
        (N : ℝ) * Real.log ε := by
  have hoff : equilibriumOrderedOffDiagonalSum (fun i j => equilibriumDoubleCircularKernel ε (z i) (z j)) ≤
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [hij, if_true, le_refl]
    · simp only [hij, if_false]
      exact equilibriumDoubleCircularKernel_le_log hε (fun he => hij (hz he))
  rw [equilibriumFullSum_eq_offDiagonal_add_diagonal]
  simp only [equilibriumDoubleCircularKernel_self hε, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg, ← sub_eq_add_neg]
  exact sub_le_sub_right hoff _

/-- The reference product energy equals the literal c_beta used by the manuscript. -/
theorem equilibriumReference_measureInteraction {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) :
    (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂(R.measure : Measure ℂ).prod R.measure) = equilibriumDensityInteraction R.density := by
  rw [integral_prod _ (equilibriumObjective_finite_logEnergy_integrable hβ R.objective_finite)]
  have he (x : ℂ) : (∫ y : ℂ, equilibriumLogKernel (x - y) ∂R.measure) =
      equilibriumDensityPotential R.density x := by
    rw [← R.density_measure]
    exact (equilibriumDensityPotential_eq_measureIntegral R.smooth.continuous.measurable
      (fun y => (R.positive y).le) x).symm
  simp_rw [he]
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun y => (R.positive y).le)]
  unfold equilibriumDensityInteraction
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => mul_comm _ _)

theorem equilibriumReference_cutoffPotential {β : ℝ} (R : EquilibriumConstructedReference β)
    (ε : ℝ) (x : ℂ) :
    (∫ y : ℂ, equilibriumCircularKernel ε (x - y) ∂R.measure) =
      equilibriumCircularPotential ε R.density x := by
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun y => (R.positive y).le)]
  unfold equilibriumCircularPotential
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => mul_comm _ _)

/-- The exact epsilon-dependent deterministic bound on every collision-free
configuration, with all reference and smearing conditions discharged. -/
theorem equilibriumReference_modulated_onsager {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (hz : Function.Injective z) {ε : ℝ} (hε : 0 < ε) :
    Real.log ε / 2 - (N : ℝ) * ε ^ 2 / 2 ≤ equilibriumModulatedEnergy R.density z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := hn.ne'
  have hμnorm := equilibriumMeasure_norm_integrable_of_secondMoment
    (equilibriumObjective_finite_secondMoment R.objective_finite)
  have hp := equilibriumCircleEmpirical_reference_repulsive hN z hε hβ R.objective_finite
  rw [equilibriumCircleEmpirical_selfEnergy hN z hε,
    equilibriumCircleEmpirical_crossEnergy hN z hε hμnorm,
    equilibriumReference_measureInteraction hβ R] at hp
  simp_rw [equilibriumReference_cutoffPotential R] at hp
  have hm := mul_nonneg (sq_nonneg (N : ℝ)) hp
  have he : (N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
      (∑ i : Fin N, ∑ j : Fin N, equilibriumDoubleCircularKernel ε (z i) (z j)) -
      2 * ((N : ℝ)⁻¹ * ∑ i : Fin N, equilibriumCircularPotential ε R.density (z i)) +
      equilibriumDensityInteraction R.density) =
      (∑ i : Fin N, ∑ j : Fin N, equilibriumDoubleCircularKernel ε (z i) (z j)) -
      2 * (N : ℝ) * (∑ i : Fin N, equilibriumCircularPotential ε R.density (z i)) +
      (N : ℝ) ^ 2 * equilibriumDensityInteraction R.density := by
    field_simp [hn0]
  rw [he] at hm
  have hL := equilibriumLogMoment_mul_integrable R.smooth.continuous.measurable
    (fun y => (R.positive y).le) R.integrable R.secondMoment_integrable
  have hu (i : Fin N) : equilibriumDensityPotential R.density (z i) - ε ^ 2 / 2 ≤
      equilibriumCircularPotential ε R.density (z i) := by
    have h := (equilibriumCircularPotential_bounds hε R.smooth.continuous.measurable
      (fun y => (R.positive y).le) R.cap R.integrable hL (z i)).1
    simpa only [inv_mul_cancel₀ Real.pi_ne_zero, one_mul] using h
  have hus := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  rw [Finset.sum_sub_distrib] at hus
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hus
  have hum := mul_le_mul_of_nonneg_left hus (by positivity : 0 ≤ 2 * (N : ℝ))
  have hsum := equilibriumDoubleCircular_sum_le z hz hε
  have hAn : 2 * (N : ℝ) * equilibriumModulatedEnergy R.density z =
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) -
      2 * (N : ℝ) * (∑ i, equilibriumDensityPotential R.density (z i)) +
      (N : ℝ) ^ 2 * equilibriumDensityInteraction R.density := by
    unfold equilibriumModulatedEnergy
    field_simp [hn0]
  nlinarith

/-- Choosing the genuine radius epsilon=N^(-1/2) gives the exact log-N scale.
This is a deterministic lower bound, not yet a uniform partition estimate. -/
theorem equilibriumReference_modulated_log_lower {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (hz : Function.Injective z) :
    -(Real.log (N : ℝ)) / 4 - 1 / 2 ≤ equilibriumModulatedEnergy R.density z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hε : 0 < (Real.sqrt (N : ℝ))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hn)
  have h := equilibriumReference_modulated_onsager hβ R hN z hz hε
  rw [Real.log_inv, Real.log_sqrt hn.le, inv_pow, Real.sq_sqrt hn.le,
    mul_inv_cancel₀ hn.ne'] at h
  linarith

/-- The exact centered representation still retains the canonical one-body
correction; it is not replaced by a pure centered U-statistic. -/
theorem equilibriumModulatedEnergy_centering {N : ℕ} (hN : 0 < N)
    (ρ : ℂ → ℝ) (z : Fin N → ℂ) :
    equilibriumModulatedEnergy ρ z =
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j) -
        equilibriumDensityPotential ρ (z i) - equilibriumDensityPotential ρ (z j) +
        equilibriumDensityInteraction ρ) / (2 * (N : ℝ)) -
      (∑ i, equilibriumDensityPotential ρ (z i)) / (N : ℝ) + equilibriumDensityInteraction ρ / 2 :=
  equilibrium_modulated_centering hN _ _ _

end RepulsiveCoulomb
