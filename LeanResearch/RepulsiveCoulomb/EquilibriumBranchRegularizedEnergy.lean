import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSmoothedKernelIdentity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDoubleErrorStructure
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchOnsager

/-! Actual doubly regularized canonical energy. Both reference terms use the
same double-circle kernel as the particle pairs. Product integrability and
its exact correspondence with the two smeared measures precede the lower
bound A_(N,epsilon)>=log(epsilon)/2. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

theorem equilibriumReference_double_error_product_integrable {β : ℝ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => equilibriumDoubleCircularError ε p.1 p.2)
      ((R.measure : Measure ℂ).prod R.measure) := by
  have hm := equilibriumDoubleCircularError_joint_measurable hε
  have hrows (x : ℂ) : Integrable (equilibriumDoubleCircularError ε x) R.measure := by
    simpa only [pow_one] using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).1
  have hrowbound (x : ℂ) : (∫ y : ℂ, equilibriumDoubleCircularError ε x y ∂R.measure) ≤ 4 * ε ^ 2 := by
    simpa only [pow_one, Nat.sub_self, pow_zero, one_mul, Nat.factorial_one, Nat.cast_one, mul_one]
      using (equilibriumReference_double_error_power R hε 1 (by norm_num) x).2
  have hnorm : Integrable (fun x : ℂ => ∫ y : ℂ, ‖equilibriumDoubleCircularError ε x y‖ ∂R.measure) R.measure := by
    apply (integrable_const (4 * ε ^ 2)).mono'
      hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have he : (∫ y : ℂ, ‖equilibriumDoubleCircularError ε x y‖ ∂R.measure) =
          ∫ y : ℂ, equilibriumDoubleCircularError ε x y ∂R.measure := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by
          change ‖equilibriumDoubleCircularError ε x y‖ = equilibriumDoubleCircularError ε x y
          rw [Real.norm_eq_abs, abs_of_nonneg (equilibriumDoubleCircularError_nonneg ε x y)])
      rw [he]
      exact hrowbound x)
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨Eventually.of_forall hrows, hnorm⟩

/-- The genuine double kernel is absolutely integrable on the original product
reference; the proxy identity is used only on the proved product-null diagonal complement. -/
theorem equilibriumReference_double_kernel_product_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => equilibriumDoubleCircularKernel ε p.1 p.2)
      ((R.measure : Measure ℂ).prod R.measure) := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ R.objective_finite
  letI : NullSingletonClass (R.measure : Measure ℂ) := ⟨fun x => hAC (measure_singleton x)⟩
  have hne : ∀ᵐ p : ℂ × ℂ ∂(R.measure : Measure ℂ).prod R.measure, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall (fun x => ((R.measure : Measure ℂ).ae_ne x).mono (fun _ hy => hy.symm))
  apply ((equilibriumObjective_finite_logEnergy_integrable hβ R.objective_finite).sub
    (equilibriumReference_double_error_product_integrable R hε)).congr
  filter_upwards [hne] with p hp
  dsimp only [Pi.sub_apply]
  rw [equilibriumDoubleCircularError_eq_sub hε hp]
  ring

/-- The canonical energy with the same double kernel in its particle, cross,
and reference self terms. -/
def equilibriumRegularizedModulatedEnergy {β : ℝ} {N : ℕ} (ε : ℝ)
    (R : EquilibriumConstructedReference β) (z : Fin N → ℂ) : ℝ :=
  equilibriumOrderedOffDiagonalSum (fun i j => equilibriumDoubleCircularKernel ε (z i) (z j)) /
    (2 * (N : ℝ)) -
    (∑ i : Fin N, ∫ y : ℂ, equilibriumDoubleCircularKernel ε (z i) y ∂R.measure) +
    (N : ℝ) / 2 * (∫ x : ℂ, ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure ∂R.measure)

/-- Nelson-ready regularized lower bound. It uses positivity against the
actually smeared reference, and is valid even at repeated particle positions
because the double kernel retains its finite self-energy on the diagonal. -/
theorem equilibriumReference_regularized_modulated_lower {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) {ε : ℝ} (hε : 0 < ε) :
    Real.log ε / 2 ≤ equilibriumRegularizedModulatedEnergy ε R z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := hn.ne'
  have hp := equilibriumReference_double_smoothed_repulsive hβ R hN z hε
  rw [equilibriumCircleEmpirical_selfEnergy hN z hε,
    equilibriumReference_double_smoothed_crossEnergy hβ R hN z hε,
    equilibriumReference_double_smoothed_selfEnergy hβ R hε] at hp
  rw [equilibriumFullSum_eq_offDiagonal_add_diagonal] at hp
  simp only [equilibriumDoubleCircularKernel_self hε, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hp
  have h := mul_nonneg (by positivity : 0 ≤ (N : ℝ) / 2) hp
  have he : (N : ℝ) / 2 *
      ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
        (equilibriumOrderedOffDiagonalSum (fun i j => equilibriumDoubleCircularKernel ε (z i) (z j)) +
          (N : ℝ) * -Real.log ε) -
        2 * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∫ y : ℂ, equilibriumDoubleCircularKernel ε (z i) y ∂R.measure) +
        (∫ x : ℂ, ∫ y : ℂ, equilibriumDoubleCircularKernel ε x y ∂R.measure ∂R.measure)) =
      equilibriumRegularizedModulatedEnergy ε R z - Real.log ε / 2 := by
    unfold equilibriumRegularizedModulatedEnergy
    field_simp [hn0]
    ring
  rw [he] at h
  linarith

end RepulsiveCoulomb
