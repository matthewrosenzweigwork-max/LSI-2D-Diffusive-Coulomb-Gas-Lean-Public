import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductExponential
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral

/-! The authored one-body product-power intermediate and the actual
concavity of x^(1/N). All displayed real integrals are genuinely integrable. -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem paper_exp_div_nat_integrable {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    {N : ℕ} (hN : 0 < N) : Integrable (fun x => Real.exp (f x / (N : ℝ))) μ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : Measurable (fun x => Real.exp (f x / (N : ℝ))) := (hfm.div_const _).exp
  apply ((integrable_const (1 : ℝ)).add hfi).mono' hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  change Real.exp (f x / (N : ℝ)) ≤ 1 + Real.exp (f x)
  by_cases hx : 0 ≤ f x
  · have hmul := mul_le_mul_of_nonneg_left hn1 hx
    have hd : f x / (N : ℝ) ≤ f x := (div_le_iff₀ hn).mpr (by nlinarith)
    have he := Real.exp_le_exp.mpr hd
    linarith
  · have hd : f x / (N : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) hn.le
    have he : Real.exp (f x / (N : ℝ)) ≤ 1 := by simpa using Real.exp_le_exp.mpr hd
    linarith [Real.exp_pos (f x)]

/-- Genuine integral factorization before any concavity reduction. -/
theorem paper_product_exp_average_power {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : Fin N → ℂ => Real.exp ((∑ i, f (z i)) / (N : ℝ)))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ z : Fin N → ℂ, Real.exp ((∑ i, f (z i)) / (N : ℝ))
      ∂Measure.pi (fun _ : Fin N => μ)) =
        (∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ) ^ N := by
  have hi := paper_exp_div_nat_integrable hfm hfi hN
  have he : (fun z : Fin N → ℂ => Real.exp ((∑ i, f (z i)) / (N : ℝ))) =
      (fun z : Fin N → ℂ => ∏ i, Real.exp (f (z i) / (N : ℝ))) := by
    funext z
    rw [Finset.sum_div, Real.exp_sum]
  rw [he]
  refine ⟨Integrable.fintype_prod (fun _ : Fin N => hi), ?_⟩
  simpa only [Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin N) (fun x : ℂ => Real.exp (f x / (N : ℝ))))

/-- This is the manuscript's concavity application, explicitly to x^(1/N),
not the distinct pointwise finite-coordinate Jensen argument. -/
theorem paper_exp_integral_inverse_power_concavity {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    {N : ℕ} (hN : 0 < N) :
    (∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ) ≤
      (∫ x : ℂ, Real.exp (f x) ∂μ) ^ (1 / (N : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hp1 : 1 / (N : ℝ) ≤ 1 := (div_le_one hn).mpr hn1
  have hi := paper_exp_div_nat_integrable hfm hfi hN
  have he (x : ℂ) : (Real.exp (f x)) ^ (1 / (N : ℝ)) = Real.exp (f x / (N : ℝ)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hgi : Integrable ((fun x : ℝ => x ^ (1 / (N : ℝ))) ∘ (fun x => Real.exp (f x))) μ := by
    simpa only [Function.comp_def, he] using hi
  have h := (Real.concaveOn_rpow hp0 hp1).le_map_integral
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (Eventually.of_forall (fun x => (Real.exp_pos (f x)).le)) hfi hgi
  simpa only [he] using h

theorem paper_exp_integral_power_le {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    {N : ℕ} (hN : 0 < N) :
    (∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ) ^ N ≤
      ∫ x : ℂ, Real.exp (f x) ∂μ := by
  have h := pow_le_pow_left₀
    (integral_nonneg (fun x => (Real.exp_pos (f x / (N : ℝ))).le))
    (paper_exp_integral_inverse_power_concavity hfm hfi hN) N
  simpa only [one_div, Real.rpow_inv_natCast_pow
    (integral_nonneg (fun x => (Real.exp_pos (f x)).le)) hN.ne'] using h

/-- The exact N/2 intermediate needed after Cauchy--Schwarz, followed by
its one-body half-power reduction. -/
theorem paper_exp_integral_half_power_le {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    {N : ℕ} (hN : 0 < N) :
    (∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ) ^ ((N : ℝ) / 2) ≤
      (∫ x : ℂ, Real.exp (f x) ∂μ) ^ (1 / 2 : ℝ) := by
  have hi0 : 0 ≤ ∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have h := Real.rpow_le_rpow (pow_nonneg hi0 N)
    (paper_exp_integral_power_le hfm hfi hN) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : ((∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ) ^ N) ^ (1 / 2 : ℝ) =
      (∫ x : ℂ, Real.exp (f x / (N : ℝ)) ∂μ) ^ ((N : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hi0]
    congr 1
    ring
  rwa [he] at h

end RepulsiveCoulomb.PaperRoute
