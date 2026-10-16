module

public import LeanResearch.RepulsiveCoulomb.WeightedMeanCentering
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Quantitative comparisons of actual finite-measure averages, for the dyadic
argument in Bjorn2001. These are elementary integral inequalities; no Poincare
or David--Semmes estimate is assumed or asserted here. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem norm_average_le_average_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) :
    ‖⨍ x, f x ∂μ‖ ≤ ⨍ x, ‖f x‖ ∂μ := by
  unfold average
  exact norm_integral_le_integral_norm f

theorem norm_setAverage_sub_const_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤)
    {f : X → ℝ} (hf : IntegrableOn f S μ) (c : ℝ) :
    ‖(⨍ x in S, f x ∂μ) - c‖ ≤ ⨍ x in S, ‖f x - c‖ ∂μ := by
  have hc : IntegrableOn (fun _ : X => c) S μ := integrableOn_const hSfin
  have he : (⨍ x in S, f x - c ∂μ) = (⨍ x in S, f x ∂μ) - c := by
    rw [setAverage_fun_sub hf hc, setAverage_const hS0 hSfin]
  rw [← he]
  exact norm_average_le_average_norm (μ.restrict S) (fun x => f x - c)

theorem setAverage_mono_ae_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} {f g : X → ℝ}
    (hf : IntegrableOn f S μ) (hg : IntegrableOn g S μ)
    (hfg : f ≤ᵐ[μ.restrict S] g) :
    (⨍ x in S, f x ∂μ) ≤ ⨍ x in S, g x ∂μ := by
  simp only [average_eq, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg) (inv_nonneg.mpr ENNReal.toReal_nonneg)

theorem setAverage_nonneg_subset_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S T : Set X} (hST : S ⊆ T)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤) (hT0 : μ T ≠ 0) (hTfin : μ T ≠ ⊤)
    {g : X → ℝ} (hg : IntegrableOn g T μ) (hgn : ∀ x, 0 ≤ g x) :
    (⨍ x in S, g x ∂μ) ≤ (μ.real T / μ.real S) * ⨍ x in T, g x ∂μ := by
  have hm := setIntegral_mono_set hg (Eventually.of_forall hgn) (Eventually.of_forall hST)
  have hS : μ.real S ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hS0, hSfin⟩
  have hT : μ.real T ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hT0, hTfin⟩
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  change (μ.real S)⁻¹ * (∫ x in S, g x ∂μ) ≤
    (μ.real T / μ.real S) * ((μ.real T)⁻¹ * ∫ x in T, g x ∂μ)
  calc
    _ ≤ (μ.real S)⁻¹ * ∫ x in T, g x ∂μ :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = _ := by field_simp

theorem norm_nested_average_difference_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S T : Set X} (hST : S ⊆ T)
    (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤) (hT0 : μ T ≠ 0) (hTfin : μ T ≠ ⊤)
    {f : X → ℝ} (hf : IntegrableOn f T μ) :
    ‖(⨍ x in S, f x ∂μ) - (⨍ x in T, f x ∂μ)‖ ≤
      (μ.real T / μ.real S) * ⨍ x in T, ‖f x - (⨍ y in T, f y ∂μ)‖ ∂μ := by
  apply (norm_setAverage_sub_const_le μ hS0 hSfin (hf.mono_set hST) _).trans
  exact setAverage_nonneg_subset_bound μ hST hS0 hSfin hT0 hTfin
    (hf.sub (integrableOn_const hTfin)).norm (fun x => norm_nonneg _)

end RepulsiveCoulomb
