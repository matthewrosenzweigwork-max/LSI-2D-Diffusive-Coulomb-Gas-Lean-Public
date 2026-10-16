import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison

/-! Normalized integral comparison under actual two-sided measure bounds.
The global density normalization cancels in the ratio C/c. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem normalized_integral_ratio_bound {I J M N c C : ℝ}
    (hI : 0 ≤ I) (hM : 0 < M) (hN : 0 < N) (hc : 0 < c) (hC : 0 ≤ C)
    (hJ : J ≤ C * I) (hmass : c * M ≤ N) :
    J / N ≤ (C / c) * (I / M) := by
  have he : (C / c) * (I / M) = (C * I) / (c * M) := by ring
  rw [he]
  apply (div_le_div_iff₀ hN (mul_pos hc hM)).mpr
  calc
    J * (c * M) ≤ (C * I) * (c * M) := mul_le_mul_of_nonneg_right hJ (mul_nonneg hc.le hM.le)
    _ ≤ (C * I) * N := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hI)

theorem average_le_of_measure_comparison {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] [NeZero ν]
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlo : ENNReal.ofReal c • μ ≤ ν) (hup : ν ≤ ENNReal.ofReal C • μ)
    {g : X → ℝ} (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) :
    (⨍ x, g x ∂ν) ≤ (C / c) * (⨍ x, g x ∂μ) := by
  have hi := integral_mono_measure hup (Eventually.of_forall hgn) (hg.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul] at hi
  have hm := ENNReal.toReal_mono (measure_ne_top ν univ) (hlo univ)
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at hm
  rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul]
  rw [mul_comm (ν.real univ)⁻¹, ← div_eq_mul_inv,
    mul_comm (μ.real univ)⁻¹, ← div_eq_mul_inv]
  exact normalized_integral_ratio_bound (integral_nonneg hgn) measureReal_univ_pos
    measureReal_univ_pos hc hC hi hm

end RepulsiveCoulomb
