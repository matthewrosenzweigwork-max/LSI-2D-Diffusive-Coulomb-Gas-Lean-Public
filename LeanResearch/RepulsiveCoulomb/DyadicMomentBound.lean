module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic

@[expose] public section

/-! Actual dyadic superlevel control of positive-part moments and the
superlinear summation bound used for disjoint truncation energies. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem positive_rpow_le_dyadic_levels {q : ℝ} (hq : 0 < q) (u : ℝ) :
    ENNReal.ofReal ((max u 0) ^ q) ≤ ∑' j : ℤ,
      {t : ℝ | 2 * (2 : ℝ) ^ j ≤ t}.indicator
        (fun _ => ENNReal.ofReal ((4 * (2 : ℝ) ^ j) ^ q)) u := by
  by_cases hu : u ≤ 0
  · rw [max_eq_right hu, Real.zero_rpow hq.ne', ENNReal.ofReal_zero]
    exact bot_le
  have hu0 : 0 < u := lt_of_not_ge hu
  obtain ⟨n, hn, hn'⟩ := exists_mem_Ico_zpow hu0 (by norm_num : (1 : ℝ) < 2)
  have he : 2 * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ n := by
    rw [zpow_sub₀ (by norm_num), zpow_one]
    ring
  have he' : 4 * (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ (n + 1) := by
    rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num), zpow_one]
    ring
  apply le_trans _ (ENNReal.le_tsum (n - 1))
  rw [Set.indicator_of_mem (show u ∈ {t : ℝ | 2 * (2 : ℝ) ^ (n - 1) ≤ t} by change 2 * (2 : ℝ) ^ (n - 1) ≤ u; rwa [he])]
  rw [max_eq_left hu0.le, he']
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hu0.le hn'.le hq.le)

theorem positive_moment_le_dyadic_levels {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u : X → ℝ} (hu : Measurable u) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, ENNReal.ofReal ((max (u x) 0) ^ q) ∂μ) ≤
      ∑' j : ℤ, ENNReal.ofReal ((4 * (2 : ℝ) ^ j) ^ q) * μ {x | 2 * (2 : ℝ) ^ j ≤ u x} := by
  have h := lintegral_mono (μ := μ) (fun x => positive_rpow_le_dyadic_levels hq (u x))
  change _ ≤ ∫⁻ x, ∑' j : ℤ,
    {z | 2 * (2 : ℝ) ^ j ≤ u z}.indicator
      (fun _ => ENNReal.ofReal ((4 * (2 : ℝ) ^ j) ^ q)) x ∂μ at h
  rw [lintegral_tsum (fun j =>
    (measurable_const.indicator (measurableSet_le measurable_const hu)).aemeasurable)] at h
  simpa only [lintegral_indicator (measurableSet_le measurable_const hu), lintegral_const,
    Measure.restrict_apply_univ] using h

theorem tsum_rpow_le_of_tsum_le {ι : Type*} {e : ι → ℝ≥0∞} {E : ℝ≥0∞}
    {κ : ℝ} (hκ : 1 ≤ κ) (hE : ∑' j, e j ≤ E) : ∑' j, (e j) ^ κ ≤ E ^ κ := by
  have hκ0 : 0 ≤ κ - 1 := by linarith
  have he (x : ℝ≥0∞) : x ^ κ = x * x ^ (κ - 1) := by
    calc
      x ^ κ = x ^ (1 + (κ - 1)) := by congr 1; ring
      _ = x * x ^ (κ - 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) hκ0, ENNReal.rpow_one]
  calc
    _ ≤ ∑' j, e j * E ^ (κ - 1) := by
      apply ENNReal.tsum_le_tsum
      intro j
      rw [he]
      exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ((ENNReal.le_tsum j).trans hE) hκ0)
    _ = (∑' j, e j) * E ^ (κ - 1) := ENNReal.tsum_mul_right
    _ ≤ E * E ^ (κ - 1) := mul_le_mul' hE le_rfl
    _ = E ^ κ := (he E).symm

end RepulsiveCoulomb
