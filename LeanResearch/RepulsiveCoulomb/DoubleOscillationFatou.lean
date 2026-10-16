module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

/-! Fatou transfer of eventually valid integral bounds to an actual pointwise
a.e. limit. All quantities remain in ENNReal until later normalization. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem lintegral_le_of_ae_tendsto_of_eventually_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞} {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ᶠ n in atTop, (∫⁻ x, F n x ∂μ) ≤ b n)
    (hb : Tendsto b atTop (𝓝 B)) : (∫⁻ x, f x ∂μ) ≤ B := by
  calc
    _ = ∫⁻ x, liminf (fun n => F n x) atTop ∂μ :=
      lintegral_congr_ae (hlim.mono (fun _ h => h.liminf_eq.symm))
    _ ≤ liminf (fun n => ∫⁻ x, F n x ∂μ) atTop := lintegral_liminf_le' hF
    _ ≤ liminf b atTop := Filter.liminf_le_liminf hbound
    _ = B := hb.liminf_eq

end RepulsiveCoulomb
