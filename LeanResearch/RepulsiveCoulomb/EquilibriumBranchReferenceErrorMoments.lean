module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDoubleCircular
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchErrorMoments

@[expose] public section

/-! The checked planar error moments transferred to the actual thermal law.
The sharp uniform density cap removes pi and all temperature dependence.
Product integrability with a singular circle is derived by Fubini domination. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumReference_error_power_integrable {β : ℝ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumCircularError ε (x - y) ^ p) R.measure := by
  rw [← R.density_measure]
  apply (equilibriumDensityMeasure_integrable_iff R.smooth.continuous.measurable
    (fun y => (R.positive y).le) _).mpr
  simpa only [equilibriumCircularError_sub_symm ε x, mul_comm] using
    equilibriumCircularError_pow_mul_integrable hε p hp R.smooth.continuous.measurable
      (fun y => (R.positive y).le) R.cap x

theorem equilibriumReference_error_power_bound {β : ℝ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (x : ℂ) :
    (∫ y : ℂ, equilibriumCircularError ε (x - y) ^ p ∂R.measure) ≤
      2 * (p.factorial : ℝ) * ε ^ 2 := by
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun y => (R.positive y).le)]
  have he : (∫ y : ℂ, R.density y * equilibriumCircularError ε (x - y) ^ p) =
      ∫ y : ℂ, equilibriumCircularError ε (y - x) ^ p * R.density y := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by
      change R.density y * equilibriumCircularError ε (x - y) ^ p =
        equilibriumCircularError ε (y - x) ^ p * R.density y
      rw [equilibriumCircularError_sub_symm]
      ring)
  rw [he]
  calc
    _ ≤ 2 * Real.pi * (p.factorial : ℝ) * ε ^ 2 * Real.pi⁻¹ :=
      integral_equilibriumCircularError_pow_mul_le hε p hp R.smooth.continuous.measurable
        (fun y => (R.positive y).le) R.cap x
    _ = _ := by field_simp <;> ring

/-- Actual product-space absolute integrability, rather than assuming every
higher angular log moment is already known at each exceptional spatial row. -/
theorem equilibriumReference_circle_error_power_integrable {β : ℝ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (c : ℂ) :
    Integrable (fun q : ℂ × ℂ => equilibriumCircularError ε (q.1 - q.2) ^ p)
      ((equilibriumCircleMeasure c ε).prod R.measure) := by
  have hm : Measurable (fun q : ℂ × ℂ => equilibriumCircularError ε (q.1 - q.2) ^ p) :=
    ((equilibriumCircularError_measurable ε).comp (measurable_fst.sub measurable_snd)).pow_const p
  have hrows : ∀ᵐ z ∂equilibriumCircleMeasure c ε,
      Integrable (fun y : ℂ => equilibriumCircularError ε (z - y) ^ p) R.measure :=
    Eventually.of_forall (equilibriumReference_error_power_integrable R hε p hp)
  have hnorm : Integrable (fun z : ℂ =>
      ∫ y : ℂ, ‖equilibriumCircularError ε (z - y) ^ p‖ ∂R.measure)
      (equilibriumCircleMeasure c ε) := by
    apply (integrable_const (2 * (p.factorial : ℝ) * ε ^ 2)).mono'
      hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have he : (∫ y : ℂ, ‖equilibriumCircularError ε (z - y) ^ p‖ ∂R.measure) =
          ∫ y : ℂ, equilibriumCircularError ε (z - y) ^ p ∂R.measure := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by
          change ‖equilibriumCircularError ε (z - y) ^ p‖ = equilibriumCircularError ε (z - y) ^ p
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (equilibriumCircularError_nonneg ε _) p)])
      rw [he]
      exact equilibriumReference_error_power_bound R hε p hp z)
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨hrows, hnorm⟩

end RepulsiveCoulomb
