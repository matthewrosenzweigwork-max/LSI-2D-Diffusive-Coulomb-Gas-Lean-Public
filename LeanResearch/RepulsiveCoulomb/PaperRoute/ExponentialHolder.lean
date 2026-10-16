module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Genuine probability-space Hölder interpolation for exponential moments.
Finiteness is proved from the larger-coupling integral before the real-valued
integral inequality is used. No lower bound of one for a partition is assumed. -/
noncomputable section
open MeasureTheory Real
namespace RepulsiveCoulomb.PaperRoute

/-- Actual Hölder, with exponent `T/t`, interpolates the exponential integral.
The statement includes the needed integrability, rather than comparing
Bochner integrals whose junk defaults might hide a divergent moment. -/
theorem exponential_integral_holder {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {A : α → ℝ} (hA : Measurable A)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hT : Integrable (fun x => Real.exp (-T * A x)) μ) :
    Integrable (fun x => Real.exp (-t * A x)) μ ∧
      (∫ x, Real.exp (-t * A x) ∂μ) ≤
        (∫ x, Real.exp (-T * A x) ∂μ) ^ (t / T) := by
  rcases htT.eq_or_lt with rfl | hlt
  · simpa [div_self ht.ne'] using And.intro hT (le_refl (∫ x, Real.exp (-t * A x) ∂μ))
  have hTpos : 0 < T := ht.trans hlt
  let p : ℝ := T / t
  have hp : 1 < p := (one_lt_div ht).mpr hlt
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hconj := Real.HolderConjugate.conjExponent hp
  have hm : AEStronglyMeasurable (fun x => Real.exp (-t * A x)) μ :=
    (measurable_const.mul hA).exp.aestronglyMeasurable
  have hpow (x : α) : (Real.exp (-t * A x)) ^ p = Real.exp (-T * A x) := by
    rw [← Real.exp_mul]
    congr 1
    dsimp [p]
    field_simp
  have hf : MemLp (fun x => Real.exp (-t * A x)) (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hm (by simp [hp0]) ENNReal.ofReal_ne_top).mp
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le,
      ENNReal.toReal_ofReal hp0.le, hpow] using hT
  have hi := MemLp.integrable (show (1 : ENNReal) ≤ ENNReal.ofReal p by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le) hf
  refine ⟨hi, ?_⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-t * A x)).le))
    (Filter.Eventually.of_forall (fun _ : α => (zero_le_one : (0 : ℝ) ≤ 1))) hf
    (memLp_const (1 : ℝ))
  have he : 1 / p = t / T := by dsimp [p]; field_simp
  simpa only [mul_one, hpow, Real.one_rpow, integral_const, probReal_univ,
    one_smul, he] using hh

/-- A common lower-coupling bound is `max 1 C`, whether or not the fixed
coupling partition is at least one. -/
theorem exponential_integral_le_max_of_holder {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {A : α → ℝ} (hA : Measurable A)
    {t T C : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hT : Integrable (fun x => Real.exp (-T * A x)) μ)
    (hC : (∫ x, Real.exp (-T * A x) ∂μ) ≤ C) :
    (∫ x, Real.exp (-t * A x) ∂μ) ≤ max 1 C := by
  have hTpos : 0 < T := ht.trans_le htT
  have hn : 0 ≤ ∫ x, Real.exp (-T * A x) ∂μ :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hθ : 0 ≤ t / T := div_nonneg ht.le hTpos.le
  have hθ1 : t / T ≤ 1 := (div_le_one hTpos).mpr htT
  exact (exponential_integral_holder μ hA ht htT hT).2.trans
    ((Real.rpow_le_rpow hn (hC.trans (le_max_right _ _)) hθ).trans
      (Real.rpow_le_self_of_one_le (le_max_left _ _) hθ1))

end RepulsiveCoulomb.PaperRoute
