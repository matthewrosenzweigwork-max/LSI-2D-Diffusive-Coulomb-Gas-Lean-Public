import LeanResearch.RepulsiveCoulomb.EquilibriumBranchConstructedReference
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual product-reference densities. This is a new records-only
reconstruction after the 2026-10-01 workspace recovery; it is not asserted
byte-identical to the lost earlier draft and has not been compiled. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def equilibriumProductDensity (N : ℕ) (ρ : ℂ → ℝ) (z : Fin N → ℂ) : ℝ :=
  ∏ i, ρ (z i)

theorem equilibriumProductDensity_nonneg {ρ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (N : ℕ) (z : Fin N → ℂ) : 0 ≤ equilibriumProductDensity N ρ z :=
  Finset.prod_nonneg (fun _ _ => hρ0 _)

theorem equilibriumProductDensity_measurable {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (N : ℕ) : Measurable (equilibriumProductDensity N ρ) := by
  exact Finset.measurable_prod Finset.univ (fun i _ => hρm.comp (measurable_pi_apply i))

theorem equilibriumProductDensity_integrable {ρ : ℂ → ℝ} (hρi : Integrable ρ)
    (N : ℕ) : Integrable (equilibriumProductDensity N ρ)
      (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) := by
  exact Integrable.fintype_prod (fun _ : Fin N => hρi)

theorem equilibriumProductDensity_mass {ρ : ℂ → ℝ}
    (hρmass : (∫ x : ℂ, ρ x) = 1) (N : ℕ) :
    (∫ z : Fin N → ℂ, equilibriumProductDensity N ρ z
      ∂Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) = 1 := by
  change (∫ z : Fin N → ℂ, ∏ i, ρ (z i)
    ∂Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) = 1
  rw [integral_fintype_prod_eq_prod]
  simp only [hρmass, Finset.prod_const_one]

/-- The literal product law is the planar product volume with its product
Lebesgue density; no independence or change-of-measure premise is assumed. -/
theorem equilibriumDensityMeasure_pi {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) (N : ℕ) :
    Measure.pi (fun _ : Fin N => equilibriumDensityMeasure ρ) =
      (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))).withDensity
        (fun z => ENNReal.ofReal (equilibriumProductDensity N ρ z)) := by
  classical
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi : Integrable (equilibriumProductDensity N ρ)
      (Measure.pi (fun i : Fin N => (volume : Measure ℂ).restrict (s i))) :=
    Integrable.fintype_prod (fun _ : Fin N => hρi.restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (equilibriumProductDensity_nonneg hρ0 N))]
  change ENNReal.ofReal (∫ z : Fin N → ℂ, ∏ i, ρ (z i)
    ∂Measure.pi (fun i : Fin N => (volume : Measure ℂ).restrict (s i))) = _
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg hρ0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [equilibriumDensityMeasure, withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal hρi.restrict (Eventually.of_forall hρ0)

theorem equilibriumReference_product_density {β : ℝ}
    (R : EquilibriumConstructedReference β) (N : ℕ) :
    Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)) =
      (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))).withDensity
        (fun z => ENNReal.ofReal (equilibriumProductDensity N R.density z)) := by
  rw [← R.density_measure]
  exact equilibriumDensityMeasure_pi R.smooth.continuous.measurable
    (fun x => (R.positive x).le) R.integrable R.mass_one N

theorem equilibriumReference_product_density_pos {β : ℝ}
    (R : EquilibriumConstructedReference β) (N : ℕ) (z : Fin N → ℂ) :
    0 < equilibriumProductDensity N R.density z :=
  Finset.prod_pos (fun _ _ => R.positive _)

theorem equilibriumReference_product_density_exp {β : ℝ}
    (R : EquilibriumConstructedReference β) (N : ℕ) (z : Fin N → ℂ) :
    equilibriumProductDensity N R.density z = Real.exp (∑ i, Real.log (R.density (z i))) := by
  rw [Real.exp_sum]
  simp only [Real.exp_log (R.positive _)]
  rfl

end RepulsiveCoulomb
