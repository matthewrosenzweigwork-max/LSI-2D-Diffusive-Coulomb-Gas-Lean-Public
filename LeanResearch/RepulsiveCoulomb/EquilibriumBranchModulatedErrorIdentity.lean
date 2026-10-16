import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCenteredError
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductModulation

/-! Exact canonical error identity for double regularization. Potential and
self-energy differences are actual integrals, and the finite centered sum
retains -N^(-1) sum a_epsilon + b_epsilon/2. Spatial collisions are explicitly
excluded before identifying the proxy with the singular pair difference. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

theorem equilibriumReference_double_kernel_row_and_difference {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumDoubleCircularKernel ε x y) R.measure ∧
    equilibriumDensityPotential R.density x -
      (∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure) = equilibriumErrorPotential ε R x := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ R.objective_finite
  letI : NullSingletonClass (R.measure : Measure ℂ) := ⟨fun y => hAC (measure_singleton y)⟩
  have hρL := equilibriumLogMoment_mul_integrable R.smooth.continuous.measurable
    (fun y => (R.positive y).le) R.integrable R.secondMoment_integrable
  have hg : Integrable (fun y : ℂ => equilibriumLogKernel (x - y)) R.measure := by
    rw [← R.density_measure]
    apply (equilibriumDensityMeasure_integrable_iff R.smooth.continuous.measurable
      (fun y => (R.positive y).le) _).mpr
    simpa only [mul_comm] using equilibriumLogKernel_mul_integrable R.smooth.continuous.measurable
      (fun y => (R.positive y).le) R.cap R.integrable hρL x
  have he : Integrable (equilibriumDoubleCircularError ε x) R.measure := by
    simpa only [pow_one] using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).1
  have hid : (fun y : ℂ => equilibriumLogKernel (x - y) - equilibriumDoubleCircularError ε x y) =ᵐ[(R.measure : Measure ℂ)]
      (fun y : ℂ => equilibriumDoubleCircularKernel ε x y) := by
    filter_upwards [(R.measure : Measure ℂ).ae_ne x] with y hy
    change equilibriumLogKernel (x - y) - equilibriumDoubleCircularError ε x y =
      equilibriumDoubleCircularKernel ε x y
    rw [equilibriumDoubleCircularError_eq_sub hε hy.symm]
    ring
  have hD := (hg.sub he).congr hid
  refine ⟨hD, ?_⟩
  have hU : equilibriumDensityPotential R.density x =
      ∫ y : ℂ, equilibriumLogKernel (x - y) ∂R.measure := by
    rw [← R.density_measure]
    exact equilibriumDensityPotential_eq_measureIntegral R.smooth.continuous.measurable
      (fun y => (R.positive y).le) x
  rw [hU, ← integral_congr_ae hid, integral_sub hg he]
  unfold equilibriumErrorPotential
  ring

/-- The reference self-energy difference is the actual mean of the error
potential; no N-dependent reference correction is omitted. -/
theorem equilibriumReference_double_self_difference {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) :
    equilibriumDensityInteraction R.density -
      (∫ x : ℂ, ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure ∂R.measure) =
        equilibriumErrorMean ε R := by
  have hu := equilibriumReference_potential_measure_integrable hβ R
  have hD := (equilibriumReference_double_kernel_product_integrable hβ R hε).integral_prod_left
  rw [← integral_equilibriumReference_potential R, ← integral_sub hu hD]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (equilibriumReference_double_kernel_row_and_difference hβ R hε x).2)

/-- The complete canonical difference and centered fluctuation formula, on the
actual collision-free domain. -/
theorem equilibriumReference_modulated_error_identity {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) (hz : Function.Injective z) :
    equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z =
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumCenteredError ε R (z i) (z j)) /
        (2 * (N : ℝ)) -
      (∑ i : Fin N, equilibriumErrorPotential ε R (z i)) / (N : ℝ) + equilibriumErrorMean ε R / 2 := by
  have hp : equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) -
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumDoubleCircularKernel ε (z i) (z j)) =
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumDoubleCircularError ε (z i) (z j)) := by
    unfold equilibriumOrderedOffDiagonalSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp only [hij, if_true, sub_self]
    · simp only [hij, if_false]
      exact (equilibriumDoubleCircularError_eq_sub hε (fun h => hij (hz h))).symm
  have hu : (∑ i : Fin N, equilibriumDensityPotential R.density (z i)) -
      (∑ i : Fin N, ∫ y : ℂ, equilibriumDoubleCircularKernel ε (z i) y ∂R.measure) =
      ∑ i : Fin N, equilibriumErrorPotential ε R (z i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (equilibriumReference_double_kernel_row_and_difference hβ R hε (z i)).2
  have hc := equilibriumReference_double_self_difference hβ R hε
  have hraw : equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z =
      (equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) -
        equilibriumOrderedOffDiagonalSum (fun i j => equilibriumDoubleCircularKernel ε (z i) (z j))) /
        (2 * (N : ℝ)) -
      ((∑ i : Fin N, equilibriumDensityPotential R.density (z i)) -
        (∑ i : Fin N, ∫ y : ℂ, equilibriumDoubleCircularKernel ε (z i) y ∂R.measure)) +
      (N : ℝ) * (equilibriumDensityInteraction R.density -
        (∫ x : ℂ, ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure ∂R.measure)) / 2 := by
    unfold equilibriumModulatedEnergy equilibriumRegularizedModulatedEnergy
    ring
  rw [hraw, hp, hu, hc]
  exact equilibrium_modulated_centering hN
    (fun i j => equilibriumDoubleCircularError ε (z i) (z j))
    (fun i => equilibriumErrorPotential ε R (z i)) (equilibriumErrorMean ε R)

end RepulsiveCoulomb
