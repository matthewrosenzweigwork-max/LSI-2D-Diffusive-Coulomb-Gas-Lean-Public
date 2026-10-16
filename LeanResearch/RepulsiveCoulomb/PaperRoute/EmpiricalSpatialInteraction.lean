import LeanResearch.RepulsiveCoulomb.PaperRoute.SignedProductExpansion
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic

/-! Additive experimental source; verification is recorded separately in evidence. The empirical measure
is literal; the energy is an actual signed-product integral restricted off
the spatial diagonal. Evaluation is scoped to injective configurations. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

def paperCountingMeasure {N : ℕ} (z : Fin N → ℂ) : Measure ℂ :=
  ∑ i, Measure.dirac (z i)

instance {N : ℕ} (z : Fin N → ℂ) : IsFiniteMeasure (paperCountingMeasure z) := by
  unfold paperCountingMeasure
  infer_instance

def paperEmpiricalMeasure {N : ℕ} (z : Fin N → ℂ) : Measure ℂ :=
  ENNReal.ofReal ((N : ℝ)⁻¹) • paperCountingMeasure z

instance {N : ℕ} (z : Fin N → ℂ) : IsFiniteMeasure (paperEmpiricalMeasure z) := by
  constructor
  simp only [paperEmpiricalMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

def paperSpatialOffDiagonal : Set (ℂ × ℂ) := {p | p.1 ≠ p.2}

theorem paperSpatialOffDiagonal_measurable : MeasurableSet paperSpatialOffDiagonal :=
  (isClosed_eq continuous_fst continuous_snd).measurableSet.compl

def paperSpatialLogKernel (p : ℂ × ℂ) : ℝ := equilibriumLogKernel (p.1 - p.2)

def paperSpatialModulatedF {N : ℕ} (μ : Measure ℂ) [IsFiniteMeasure μ]
    (z : Fin N → ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∫ᵛ p in paperSpatialOffDiagonal, paperSpatialLogKernel p
    ∂<•paperSignedSquare ((paperEmpiricalMeasure z).toSignedMeasure - μ.toSignedMeasure)

def paperSpatialModulatedEnergy {N : ℕ} (μ : Measure ℂ) [IsFiniteMeasure μ]
    (z : Fin N → ℂ) : ℝ := (N : ℝ) * paperSpatialModulatedF μ z

def paperFluctuationMeasure {N : ℕ} (μ : Measure ℂ) [IsFiniteMeasure μ]
    (z : Fin N → ℂ) : SignedMeasure ℂ :=
  Real.sqrt (N : ℝ) • ((paperEmpiricalMeasure z).toSignedMeasure - μ.toSignedMeasure)

/-- The fluctuation is sqrt(N)*(empirical-mu), and its half-interaction is
literally N*F_N. This checks the normalization on the genuine tensor square. -/
theorem paper_fluctuation_half_interaction {N : ℕ} (μ : Measure ℂ) [IsFiniteMeasure μ]
    (z : Fin N → ℂ) :
    (1 / 2 : ℝ) * (∫ᵛ p in paperSpatialOffDiagonal, paperSpatialLogKernel p
      ∂<•paperSignedSquare (paperFluctuationMeasure μ z)) = paperSpatialModulatedEnergy μ z := by
  simp only [paperFluctuationMeasure, paper_signed_square_smul,
    Real.mul_self_sqrt (Nat.cast_nonneg N), VectorMeasure.restrict_smul,
    VectorMeasure.integral_smul_vectorMeasure, smul_eq_mul,
    paperSpatialModulatedEnergy, paperSpatialModulatedF]
  ring

private theorem count_integrable {N : ℕ} (z : Fin N → ℂ) (f : ℂ → ℝ) :
    Integrable f (paperCountingMeasure z) := by
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact integrable_dirac (by finiteness)

private theorem count_integral {N : ℕ} (z : Fin N → ℂ) (f : ℂ → ℝ) :
    (∫ x, f x ∂paperCountingMeasure z) = ∑ i, f (z i) := by
  rw [paperCountingMeasure, integral_finsetSum_measure (fun i _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac]

/-- The literal finite empirical measure has unit mass when N is positive. -/
theorem paper_empirical_probability {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) :
    IsProbabilityMeasure (paperEmpiricalMeasure z) := by
  apply isProbabilityMeasure_iff_real.mpr
  have hi : (∫ _ : ℂ, (1 : ℝ) ∂paperEmpiricalMeasure z) = 1 := by
    rw [paperEmpiricalMeasure, integral_smul_measure, count_integral]
    simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg N)),
      smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')
  simpa only [integral_const, smul_eq_mul, mul_one] using hi

/-- Correctly normalized fluctuations have actual total signed mass zero. -/
theorem paper_fluctuation_total_mass {N : ℕ} (hN : 0 < N)
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (z : Fin N → ℂ) :
    paperFluctuationMeasure μ z Set.univ = 0 := by
  let : IsProbabilityMeasure (paperEmpiricalMeasure z) := paper_empirical_probability hN z
  simp only [paperFluctuationMeasure, _root_.smul_apply, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ, probReal_univ,
    sub_self, smul_zero]

private theorem count_left_integrable {N : ℕ} (z : Fin N → ℂ) (μ : Measure ℂ)
    [IsFiniteMeasure μ] {K : ℂ × ℂ → ℝ} (hK : Measurable K)
    (hrow : ∀ x, Integrable (fun y => K (x,y)) μ) :
    Integrable K ((paperCountingMeasure z).prod μ) := by
  apply (integrable_prod_iff hK.aestronglyMeasurable).mpr
  exact ⟨Eventually.of_forall hrow, count_integrable z _⟩

private theorem count_right_integrable {N : ℕ} (z : Fin N → ℂ) (μ : Measure ℂ)
    [IsFiniteMeasure μ] {K : ℂ × ℂ → ℝ} (hK : Measurable K)
    (hcol : ∀ y, Integrable (fun x => K (x,y)) μ) :
    Integrable K (μ.prod (paperCountingMeasure z)) := by
  apply (integrable_prod_iff' hK.aestronglyMeasurable).mpr
  exact ⟨Eventually.of_forall hcol, count_integrable z _⟩

private theorem count_pair_integrable {N : ℕ} (z : Fin N → ℂ)
    {K : ℂ × ℂ → ℝ} (hK : Measurable K) :
    Integrable K ((paperCountingMeasure z).prod (paperCountingMeasure z)) :=
  count_left_integrable z _ hK (fun _ => count_integrable z _)

private theorem offdiag_row_eq {μ : Measure ℂ} [NullSingletonClass μ]
    (K : ℂ × ℂ → ℝ) (x : ℂ) :
    (fun y => paperSpatialOffDiagonal.indicator K (x,y)) =ᵐ[μ] (fun y => K (x,y)) := by
  filter_upwards [μ.ae_ne x] with y hy
  exact Set.indicator_of_mem (show (x,y) ∈ paperSpatialOffDiagonal from hy.symm) _

private theorem offdiag_col_eq {μ : Measure ℂ} [NullSingletonClass μ]
    (K : ℂ × ℂ → ℝ) (y : ℂ) :
    (fun x => paperSpatialOffDiagonal.indicator K (x,y)) =ᵐ[μ] (fun x => K (x,y)) := by
  filter_upwards [μ.ae_ne y] with x hx
  exact Set.indicator_of_mem (show (x,y) ∈ paperSpatialOffDiagonal from hx) _

private theorem offdiag_product_eq {μ : Measure ℂ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (K : ℂ × ℂ → ℝ) : paperSpatialOffDiagonal.indicator K =ᵐ[μ.prod μ] K := by
  have hd : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, p ∈ paperSpatialOffDiagonal := by
    apply (Measure.ae_prod_iff_ae_ae paperSpatialOffDiagonal_measurable).mpr
    exact Eventually.of_forall (fun x => (μ.ae_ne x).mono (fun _ h => h.symm))
  filter_upwards [hd] with p hp
  exact Set.indicator_of_mem hp _

/-- Evaluation of the four positive-product spatial restrictions. Every
ordinary integral is absolutely integrable before the signed integral is
expanded. No collision convention is imposed on a repeated-label atom. -/
theorem paper_empirical_spatial_integrals {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z)
    (μ : Measure ℂ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {K : ℂ × ℂ → ℝ} (hK : Measurable K)
    (hrow : ∀ x, Integrable (fun y => K (x,y)) μ)
    (hcol : ∀ y, Integrable (fun x => K (x,y)) μ)
    (hprod : Integrable K (μ.prod μ)) :
    let E := paperEmpiricalMeasure z
    IntegrableOn K paperSpatialOffDiagonal (E.prod E) ∧
    IntegrableOn K paperSpatialOffDiagonal (E.prod μ) ∧
    IntegrableOn K paperSpatialOffDiagonal (μ.prod E) ∧
    IntegrableOn K paperSpatialOffDiagonal (μ.prod μ) ∧
    (∫ p in paperSpatialOffDiagonal, K p ∂E.prod E) =
      (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * ∑ i, ∑ j, (if i = j then 0 else K (z i,z j)) ∧
    (∫ p in paperSpatialOffDiagonal, K p ∂E.prod μ) =
      (N : ℝ)⁻¹ * ∑ i, ∫ y, K (z i,y) ∂μ ∧
    (∫ p in paperSpatialOffDiagonal, K p ∂μ.prod E) =
      (N : ℝ)⁻¹ * ∑ i, ∫ x, K (x,z i) ∂μ ∧
    (∫ p in paperSpatialOffDiagonal, K p ∂μ.prod μ) = ∫ p, K p ∂μ.prod μ := by
  classical
  let H := paperSpatialOffDiagonal.indicator K
  have hm : Measurable H := hK.indicator paperSpatialOffDiagonal_measurable
  have hr x : Integrable (fun y => H (x,y)) μ :=
    (hrow x).congr (offdiag_row_eq K x).symm
  have hc y : Integrable (fun x => H (x,y)) μ :=
    (hcol y).congr (offdiag_col_eq K y).symm
  have hAA := count_pair_integrable z hm
  have hAB := count_left_integrable z μ hm hr
  have hBA := count_right_integrable z μ hm hc
  have hBB : Integrable H (μ.prod μ) := hprod.congr (offdiag_product_eq K).symm
  have hAAs : Integrable H ((paperEmpiricalMeasure z).prod (paperEmpiricalMeasure z)) := by
    simpa only [paperEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right] using
      (hAA.smul_measure ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top
  have hABs : Integrable H ((paperEmpiricalMeasure z).prod μ) := by
    simpa only [paperEmpiricalMeasure, Measure.prod_smul_left] using hAB.smul_measure ENNReal.ofReal_ne_top
  have hBAs : Integrable H (μ.prod (paperEmpiricalMeasure z)) := by
    simpa only [paperEmpiricalMeasure, Measure.prod_smul_right] using hBA.smul_measure ENNReal.ofReal_ne_top
  refine ⟨(integrable_indicator_iff paperSpatialOffDiagonal_measurable).mp hAAs,
    (integrable_indicator_iff paperSpatialOffDiagonal_measurable).mp hABs,
    (integrable_indicator_iff paperSpatialOffDiagonal_measurable).mp hBAs,
    hprod.integrableOn, ?_, ?_, ?_, ?_⟩
  · rw [← integral_indicator paperSpatialOffDiagonal_measurable]
    change (∫ p, H p ∂(paperEmpiricalMeasure z).prod (paperEmpiricalMeasure z)) = _
    rw [paperEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right,
      integral_smul_measure, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg N)), smul_eq_mul]
    rw [integral_prod _ hAA, count_integral]
    simp_rw [count_integral]
    rw [← mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · simp [H, paperSpatialOffDiagonal, hij]
    · simp [H, paperSpatialOffDiagonal, hij, hz.ne hij]
  · rw [← integral_indicator paperSpatialOffDiagonal_measurable]
    change (∫ p, H p ∂(paperEmpiricalMeasure z).prod μ) = _
    rw [paperEmpiricalMeasure, Measure.prod_smul_left, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg N)), smul_eq_mul]
    rw [integral_prod _ hAB, count_integral]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_congr_ae (offdiag_row_eq K (z i))
  · rw [← integral_indicator paperSpatialOffDiagonal_measurable]
    change (∫ p, H p ∂μ.prod (paperEmpiricalMeasure z)) = _
    rw [paperEmpiricalMeasure, Measure.prod_smul_right, integral_smul_measure]
    simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg N)), smul_eq_mul]
    rw [integral_prod_symm _ hBA, count_integral]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_congr_ae (offdiag_col_eq K (z i))
  · rw [← integral_indicator paperSpatialOffDiagonal_measurable]
    exact integral_congr_ae (offdiag_product_eq K)

end RepulsiveCoulomb.PaperRoute
