module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GenericSmoothWeakToStrong
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-
Additive paper-route copy of the generic argument in SmoothStrongMedian.lean.
Only the imports and namespace are rerouted; the physical-gradient statement
and the mathematical hypotheses are unchanged. The original file is untouched.
-/

/-! Two-sided strong estimate about an actual median, with the physical
Euclidean energy unchanged by the two signed translations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem norm_rpow_eq_positive_parts {q : ℝ} (hq : 0 < q) (t : ℝ) :
    ‖t‖ ^ q = (max t 0) ^ q + (max (-t) 0) ^ q := by
  by_cases ht : 0 ≤ t
  · rw [Real.norm_eq_abs, abs_of_nonneg ht, max_eq_left ht,
      max_eq_right (neg_nonpos.mpr ht), Real.zero_rpow hq.ne', add_zero]
  · have hn : t ≤ 0 := (lt_of_not_ge ht).le
    rw [Real.norm_eq_abs, abs_of_nonpos hn, max_eq_right hn,
      max_eq_left (neg_nonneg.mpr hn), Real.zero_rpow hq.ne', zero_add]

theorem smooth_weak_to_strong_median (μ ν : Measure ℂ) [IsFiniteMeasure μ] [NeZero μ]
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (m : ℝ)
    (hbelow : μ.real {x | f x < m} ≤ μ.real univ / 2)
    (habove : μ.real {x | m < f x} ≤ μ.real univ / 2)
    {q κ K : ℝ} {W : ℝ≥0∞} (hq : 0 < q) (hκ : 1 ≤ κ) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (hweak : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ q) * μ {x | t < ‖v x - (⨍ z, v z ∂μ)‖} ≤
        W * (∫⁻ x, ENNReal.ofReal (‖gradient v x‖ ^ 2) ∂ν) ^ κ) :
    (∫⁻ x, ENNReal.ofReal (‖f x - m‖ ^ q) ∂μ) ≤
      2 * ENNReal.ofReal ((16 : ℝ) ^ q) * W *
        (ENNReal.ofReal (K ^ 2) * ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) ∂ν) ^ κ := by
  have hp := smooth_weak_to_strong_positive μ ν (hf.sub contDiff_const)
    (by simpa only [sub_pos] using habove) hq hκ hK0 hK hweak
  have hn := smooth_weak_to_strong_positive μ ν (contDiff_const.sub hf)
    (by simpa only [sub_pos] using hbelow) hq hκ hK0 hK hweak
  simp only [TauCeti.norm_gradient_eq_norm_fderiv, fderiv_sub_const] at hp
  simp only [TauCeti.norm_gradient_eq_norm_fderiv, fderiv_const_sub, norm_neg] at hn
  have hm : Measurable (fun x => ENNReal.ofReal ((max (f x - m) 0) ^ q)) :=
    ((Real.continuous_rpow_const hq.le).comp ((hf.continuous.sub continuous_const).max continuous_const)).measurable.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal (‖f x - m‖ ^ q)) =
      (fun x => ENNReal.ofReal ((max (f x - m) 0) ^ q) + ENNReal.ofReal ((max (m - f x) 0) ^ q)) := by
    ext x
    rw [norm_rpow_eq_positive_parts hq, neg_sub,
      ENNReal.ofReal_add (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg (le_max_right _ _) _)]
  rw [he, lintegral_add_left hm]
  have h := add_le_add hp hn
  simp only [TauCeti.norm_gradient_eq_norm_fderiv]
  convert h using 1
  rw [two_mul]
  ring

end RepulsiveCoulomb.PaperRoute
