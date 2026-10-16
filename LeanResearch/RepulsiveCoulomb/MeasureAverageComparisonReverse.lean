module

public import LeanResearch.RepulsiveCoulomb.MeasureAverageComparison

@[expose] public section

/-! Reverse actual measure and normalized-average comparison. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem reverse_measure_comparison {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlo : ENNReal.ofReal c • μ ≤ ν) (hup : ν ≤ ENNReal.ofReal C • μ) :
    ENNReal.ofReal (1 / C) • ν ≤ μ ∧ μ ≤ ENNReal.ofReal (1 / c) • ν := by
  have cancel (r : ℝ) (hr : 0 < r) : ENNReal.ofReal (1 / r) * ENNReal.ofReal r = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hr.ne', ENNReal.ofReal_one]
  constructor
  · intro S
    have h := mul_le_mul' (le_refl (ENNReal.ofReal (1 / C))) (hup S)
    simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
    rwa [← mul_assoc, cancel C hC, one_mul] at h
  · intro S
    have h := mul_le_mul' (le_refl (ENNReal.ofReal (1 / c))) (hlo S)
    simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
    rwa [← mul_assoc, cancel c hc, one_mul] at h

theorem averages_comparable_of_measure_comparison {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NeZero μ] [NeZero ν]
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlo : ENNReal.ofReal c • μ ≤ ν) (hup : ν ≤ ENNReal.ofReal C • μ)
    {g : X → ℝ} (hμ : Integrable g μ) (hν : Integrable g ν) (hgn : ∀ x, 0 ≤ g x) :
    (⨍ x, g x ∂ν) ≤ (C / c) * (⨍ x, g x ∂μ) ∧
    (⨍ x, g x ∂μ) ≤ (C / c) * (⨍ x, g x ∂ν) := by
  refine ⟨average_le_of_measure_comparison μ ν hc hC.le hlo hup hμ hgn, ?_⟩
  obtain ⟨hlo', hup'⟩ := reverse_measure_comparison μ ν hc hC hlo hup
  have h := average_le_of_measure_comparison ν μ (by positivity : 0 < 1 / C)
    (by positivity : 0 ≤ 1 / c) hlo' hup' hν hgn
  have he : (1 / c) / (1 / C) = C / c := by field_simp
  rwa [he] at h

end RepulsiveCoulomb
