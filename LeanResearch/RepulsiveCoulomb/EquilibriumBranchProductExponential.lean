module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductDensity
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Actual exponential averages on finite probability products and the
nonnegative Cauchy--Schwarz estimate used in the Gibbs defect moment.
Records-only uncompiled source; no exponential-integrability premise is
silently inferred from an ordinary integral. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem equilibrium_exp_average_le {N : ℕ} (hN : 0 < N) (a : Fin N → ℝ) :
    Real.exp ((∑ i, a i) / (N : ℝ)) ≤ (∑ i, Real.exp (a i)) / (N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ : Fin N => (N : ℝ)⁻¹)
    (p := a) (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg N))
    (by simp [hn]) (fun _ _ => mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, div_eq_inv_mul] using h

/-- Jensen before integration gives a bound independent of the number of
coordinates, with actual integrability on the product law. -/
theorem equilibriumProduct_exp_average {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : Fin N → ℂ => Real.exp ((∑ i, f (z i)) / (N : ℝ)))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ z : Fin N → ℂ, Real.exp ((∑ i, f (z i)) / (N : ℝ))
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ ∫ x : ℂ, Real.exp (f x) ∂μ := by
  let P := Measure.pi (fun _ : Fin N => μ)
  have hi (i : Fin N) : Integrable (fun z : Fin N → ℂ => Real.exp (f (z i))) P :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable hfi
  have hsum : Integrable (fun z : Fin N → ℂ => (∑ i, Real.exp (f (z i))) / (N : ℝ)) P :=
    (integrable_finsetSum Finset.univ (fun i _ => hi i)).div_const _
  have hm : Measurable (fun z : Fin N → ℂ => Real.exp ((∑ i, f (z i)) / (N : ℝ))) :=
    ((Finset.measurable_sum Finset.univ (fun i _ => hfm.comp (measurable_pi_apply i))).div_const _).exp
  have hb (z : Fin N → ℂ) := equilibrium_exp_average_le hN (fun i => f (z i))
  have hg : Integrable (fun z : Fin N → ℂ => Real.exp ((∑ i, f (z i)) / (N : ℝ))) P := by
    apply hsum.mono' hm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hb z)
  refine ⟨hg, (integral_mono hg hsum hb).trans_eq ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  have hei (i : Fin N) : (∫ z : Fin N → ℂ, Real.exp (f (z i)) ∂P) =
      ∫ x : ℂ, Real.exp (f x) ∂μ := by
    have hp := measurePreserving_eval (fun _ : Fin N => μ) i
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hfm.exp.aestronglyMeasurable]
  simp_rw [hei]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]

/-- Cauchy--Schwarz with genuine square integrability, including integrability
of the product and nonnegative real square-root powers. -/
theorem equilibrium_integral_mul_le_half_powers {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ ∧
      (∫ x, f x * g x ∂μ) ≤
        (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hfL : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hf2
  have hgL : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hg2
  refine ⟨hfL.integrable_mul hgL, ?_⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    (by simpa only [ENNReal.ofReal_ofNat] using hfL)
    (by simpa only [ENNReal.ofReal_ofNat] using hgL)
  simpa only [Real.rpow_two] using h

end RepulsiveCoulomb
