module

public import LeanResearch.RepulsiveCoulomb.PointConformalIntrinsicLength
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Length bisection and approximate metric midpoints, including curves through
zero-density punctures. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointConformal_speed_continuous {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun t ↦ pointConformalDensity a y (γ t) * ‖deriv γ t‖) :=
  ((pointConformalDensity_continuous ha y).comp hγ.continuous).mul hγ.continuous_deriv_one.norm

theorem pointConformalPathELength_eq_integral {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hst : s ≤ t) :
    pointConformalPathELength a y γ s t =
      ENNReal.ofReal (∫ u in s..t, pointConformalDensity a y (γ u) * ‖deriv γ u‖) := by
  rw [intervalIntegral.integral_of_le hst]
  rw [ofReal_integral_eq_lintegral_ofReal
    ((pointConformal_speed_continuous ha y hγ).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun u ↦ mul_nonneg (pointConformalDensity_nonneg a y _) (norm_nonneg _)))]
  simp only [pointConformalPathELength, ENNReal.ofReal_mul (pointConformalDensity_nonneg a y _)]
  rw [restrict_Ioc_eq_restrict_Icc]

theorem exists_pointConformal_path_bisection {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      pointConformalPathELength a y γ 0 t = pointConformalPathELength a y γ t 1 := by
  let f : ℝ → ℝ := fun u ↦ pointConformalDensity a y (γ u) * ‖deriv γ u‖
  have hf : Continuous f := pointConformal_speed_continuous ha y hγ
  have hn : ∀ u, 0 ≤ f u := fun u ↦ mul_nonneg (pointConformalDensity_nonneg a y _) (norm_nonneg _)
  let L := ∫ u in (0 : ℝ)..1, f u
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg (by norm_num) (fun u _ ↦ hn u)
  have hF : Continuous (fun t ↦ ∫ u in (0 : ℝ)..t, f u) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)
  have hh : L / 2 ∈ Icc (∫ u in (0 : ℝ)..0, f u) (∫ u in (0 : ℝ)..1, f u) := by
    simp only [intervalIntegral.integral_same]
    change 0 ≤ L / 2 ∧ L / 2 ≤ L
    constructor <;> linarith
  obtain ⟨t, ht, hhalf⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hF.continuousOn hh
  refine ⟨t, ht, ?_⟩
  rw [pointConformalPathELength_eq_integral ha y hγ ht.1,
    pointConformalPathELength_eq_integral ha y hγ ht.2]
  apply congrArg ENNReal.ofReal
  change (∫ u in (0 : ℝ)..t, f u) = ∫ u in t..1, f u
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) 0 t) (hf.intervalIntegrable (μ := volume) t 1)
  change (∫ u in (0 : ℝ)..t, f u) + (∫ u in t..1, f u) = L at hadd
  linarith

theorem exists_pointConformal_approximate_midpoint {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) {r : ℝ≥0∞}
    (hr : pointSmoothConformalEDist a y x z < r + r) :
    ∃ p : ℂ, pointSmoothConformalEDist a y x p < r ∧ pointSmoothConformalEDist a y p z < r := by
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
  obtain ⟨t, ht, heq⟩ := exists_pointConformal_path_bisection ha y hγ
  have hadd := pointConformalPathELength_add a y γ ht.1 ht.2
  have hlt : pointConformalPathELength a y γ 0 t < r := by
    by_contra h
    have hle := le_of_not_gt h
    have : r + r ≤ pointConformalPathELength a y γ 0 1 := by
      rw [← hadd, ← heq]
      exact add_le_add hle hle
    exact (not_lt_of_ge this) hlen
  refine ⟨γ t, ?_, ?_⟩
  · have hd := pointSmoothConformalEDist_le_path a y hγ.contDiffOn ht.1
    rw [h0] at hd
    exact hd.trans_lt hlt
  · have hd := pointSmoothConformalEDist_le_path a y hγ.contDiffOn ht.2
    rw [h1] at hd
    exact hd.trans_lt (heq ▸ hlt)

end RepulsiveCoulomb
