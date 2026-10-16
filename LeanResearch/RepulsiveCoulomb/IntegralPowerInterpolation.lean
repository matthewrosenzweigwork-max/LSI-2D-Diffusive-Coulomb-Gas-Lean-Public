import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite real integral interpolation, with genuine integrability premises. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem integral_geometric_mean_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hi : Integrable (fun x => f x ^ p * g x ^ q) μ) :
    (∫ x, f x ^ p * g x ^ q ∂μ) ≤ (∫ x, f x ∂μ) ^ p * (∫ x, g x ∂μ) ^ q := by
  have h := ENNReal.lintegral_mul_norm_pow_le hf.aemeasurable.ennreal_ofReal
    hg.aemeasurable.ennreal_ofReal hp hq hpq
  have he : (fun x => (ENNReal.ofReal (f x)) ^ p * (ENNReal.ofReal (g x)) ^ q) =
      fun x => ENNReal.ofReal (f x ^ p * g x ^ q) := by
    funext x
    rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) hp,
      ENNReal.ofReal_rpow_of_nonneg (hg0 x) hq,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) _)]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hg0 x) _))),
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) hp,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) hq,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg (integral_nonneg hf0) _) (Real.rpow_nonneg (integral_nonneg hg0) _))).mp h

theorem integral_l1_rpow_interpolation {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {r p q : ℝ} (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = 1) (he : p + r * q = 2)
    (h1 : Integrable (fun x => |f x|) μ)
    (hrint : Integrable (fun x => |f x| ^ r) μ)
    (h2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ^ 2 ∂μ) ≤ (∫ x, |f x| ∂μ) ^ p * (∫ x, |f x| ^ r ∂μ) ^ q := by
  have hid : (fun x => |f x| ^ p * (|f x| ^ r) ^ q) = fun x => f x ^ 2 := by
    funext x
    by_cases hz : f x = 0
    · simp [hz, Real.zero_rpow (ne_of_gt hp), Real.zero_rpow (ne_of_gt hq), Real.zero_rpow (ne_of_gt hr)]
    · have ha : 0 < |f x| := abs_pos.mpr hz
      rw [← Real.rpow_mul ha.le, ← Real.rpow_add ha, he, Real.rpow_two, sq_abs]
  have h := integral_geometric_mean_le hp.le hq.le hpq h1 hrint
    (fun x => abs_nonneg (f x)) (fun x => Real.rpow_nonneg (abs_nonneg (f x)) r)
    (by rwa [hid])
  rwa [hid] at h

end RepulsiveCoulomb
