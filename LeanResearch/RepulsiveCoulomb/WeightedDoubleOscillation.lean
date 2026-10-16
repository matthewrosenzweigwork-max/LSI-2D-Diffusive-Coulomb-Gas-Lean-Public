import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison

/-! L1 oscillation about an actual mean is bounded by the actual double-average
oscillation. This isolates the elementary part of Bjorn's dyadic estimates. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem average_norm_difference_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => ⨍ y, ‖f x - f y‖ ∂μ) μ := by
  have hp : Integrable (fun p : X × X => f p.1 - f p.2) (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hi := hp.integral_norm_prod_left.const_mul (μ.real univ)⁻¹
  simpa only [average_eq, smul_eq_mul] using hi

theorem mean_oscillation_le_double_average {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ} (hf : Integrable f μ) :
    (⨍ x, ‖f x - (⨍ y, f y ∂μ)‖ ∂μ) ≤ ⨍ x, ⨍ y, ‖f x - f y‖ ∂μ ∂μ := by
  have hpoint (x : X) : ‖f x - (⨍ y, f y ∂μ)‖ ≤ ⨍ y, ‖f x - f y‖ ∂μ := by
    have he : (⨍ y, f x - f y ∂μ) = f x - (⨍ y, f y ∂μ) := by
      rw [average_fun_sub (integrable_const (f x)) hf, average_const]
    rw [← he]
    exact norm_average_le_average_norm μ (fun y => f x - f y)
  have h := setAverage_mono_ae_real μ (S := univ)
    (by simpa only [IntegrableOn, Measure.restrict_univ, Pi.sub_apply] using (hf.sub (integrable_const _)).norm)
    (by simpa only [IntegrableOn, Measure.restrict_univ] using average_norm_difference_integrable μ hf)
    (Eventually.of_forall hpoint)
  simpa only [Measure.restrict_univ] using h

theorem norm_nested_average_difference_le_double {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S T : Set X} (hST : S ⊆ T)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤) (hT0 : μ T ≠ 0) (hTfin : μ T ≠ ⊤)
    {f : X → ℝ} (hf : IntegrableOn f T μ) :
    ‖(⨍ x in S, f x ∂μ) - (⨍ x in T, f x ∂μ)‖ ≤
      (μ.real T / μ.real S) * ⨍ x in T, ⨍ y in T, ‖f x - f y‖ ∂μ ∂μ := by
  letI : IsFiniteMeasure (μ.restrict T) := ⟨by simpa only [Measure.restrict_apply_univ] using hTfin.lt_top⟩
  letI : NeZero (μ.restrict T) := ⟨by
    intro h
    have he := congrArg (fun ν : Measure X => ν univ) h
    exact hT0 (by simpa using he)⟩
  exact (norm_nested_average_difference_le μ hST hS0 hSfin hT0 hTfin hf).trans
    (mul_le_mul_of_nonneg_left (mean_oscillation_le_double_average (μ.restrict T) hf)
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))

end RepulsiveCoulomb
