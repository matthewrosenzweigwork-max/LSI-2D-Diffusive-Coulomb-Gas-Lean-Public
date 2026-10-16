import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Marginal

/-! Probability-space Hölder with genuinely integrated moments and explicit
padding by the constant one. This is the analytic one-vertex input for the
ordered multigraph correlation estimate. No correlation inequality is assumed.
This records-only source has not been compiled by its author. -/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace RepulsiveCoulomb

/-- Taking a positive integer root cancels that integer power, including at
zero and infinity. -/
theorem partitionMoment_pow_root (a : ℝ≥0∞) {q : ℕ} (hq : 0 < q) :
    (a ^ q) ^ (1 / (q : ℝ)) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  rw [mul_one_div_cancel hq', ENNReal.rpow_one]

/-- At most `q` measurable factors on a probability space obey the padded
`q`-factor Hölder inequality. The missing factors are exactly constant ones. -/
theorem partitionMoment_lintegral_prod_le_roots
    {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (s : Finset E) (f : E → X → ℝ≥0∞) {q : ℕ} (hq : 0 < q)
    (hcard : s.card ≤ q) (hf : ∀ e ∈ s, Measurable (f e)) :
    (∫⁻ x, ∏ e ∈ s, f e x ∂μ) ≤
      ∏ e ∈ s, (∫⁻ x, f e x ^ q ∂μ) ^ (1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard' : (s.card : ℝ) ≤ q := by exact_mod_cast hcard
  have hsum : (∑ _e ∈ s, (1 / (q : ℝ))) = s.card / (q : ℝ) := by
    simp [nsmul_eq_mul, div_eq_mul_inv]
  have hpad : 0 ≤ 1 - s.card / (q : ℝ) := by
    have := (div_le_one hqpos).mpr hcard'
    linarith
  have hh := ENNReal.lintegral_mul_prod_norm_pow_le
    (μ := μ) s (g := fun _ : X => (1 : ℝ≥0∞))
    (f := fun e x => f e x ^ q) measurable_const.aemeasurable
    (fun e he => (hf e he).pow_const q |>.aemeasurable)
    (1 - s.card / (q : ℝ)) (p := fun _ => 1 / (q : ℝ))
    (by rw [hsum]; ring) hpad (fun _ _ => le_of_lt (one_div_pos.mpr hqpos))
  simpa only [ENNReal.one_rpow, one_mul, lintegral_const, measure_univ,
    mul_one, partitionMoment_pow_root _ hq] using hh

/-- A common bound for the actual row moment roots multiplies once for each
factor. Natural powers avoid any positivity assumptions on the bound. -/
theorem partitionMoment_lintegral_prod_le_pow
    {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (s : Finset E) (f : E → X → ℝ≥0∞) {q : ℕ} (hq : 0 < q)
    (hcard : s.card ≤ q) (hf : ∀ e ∈ s, Measurable (f e))
    (C : ℝ≥0∞)
    (hC : ∀ e ∈ s, (∫⁻ x, f e x ^ q ∂μ) ^ (1 / (q : ℝ)) ≤ C) :
    (∫⁻ x, ∏ e ∈ s, f e x ∂μ) ≤ C ^ s.card := by
  calc
    (∫⁻ x, ∏ e ∈ s, f e x ∂μ) ≤
        ∏ e ∈ s, (∫⁻ x, f e x ^ q ∂μ) ^ (1 / (q : ℝ)) :=
      partitionMoment_lintegral_prod_le_roots s f hq hcard hf
    _ ≤ ∏ _e ∈ s, C := Finset.prod_le_prod' hC
    _ = C ^ s.card := by simp

/-- The usual moment premise gives the root premise used by vertex peeling. -/
theorem partitionMoment_root_mono {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ≥0∞} {q : ℕ} (hq : 0 < q)
    {B : ℝ≥0∞} (hB : (∫⁻ x, f x ^ q ∂μ) ≤ B) :
    (∫⁻ x, f x ^ q ∂μ) ^ (1 / (q : ℝ)) ≤ B ^ (1 / (q : ℝ)) := by
  exact ENNReal.rpow_le_rpow hB (by positivity)

end RepulsiveCoulomb
