import LeanResearch.RepulsiveCoulomb.CoulombFormMeanBound
import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

/-! RECORDS-ONLY UNCHECKED DRAFT. Core selection at varying temperatures.
Only scalar norms and means are compared across the different form spaces. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombTemperature_core_sequence {N : ℕ} (β : ℕ → ℝ)
    (hβ : ∀ n, 0 < β n) (u : (n : ℕ) → CoulombFormDomain N (hβ n))
    (hu : ∀ n, ‖u n‖ = 1)
    (hm : ∀ n, poleBranchRealMean N (hβ n) (coulombFormValueL N (hβ n) (u n)) = 0)
    (hg : ∀ n, ‖coulombFormGradientL N (hβ n) (u n)‖ ≤ 1 / ((n : ℝ) + 1)) :
    ∃ φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤,
      (∀ n, ‖coulombFormCore (hβ n) (φ n) - u n‖ < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => ‖coulombFormCore (hβ n) (φ n)‖) atTop (𝓝 1) ∧
      Tendsto (fun n => ‖coulombFormGradientL N (hβ n)
        (coulombFormCore (hβ n) (φ n))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => poleBranchRealMean N (hβ n)
        (coulombFormValueL N (hβ n) (coulombFormCore (hβ n) (φ n)))) atTop (𝓝 0) := by
  classical
  choose φ hφ using fun n : ℕ => coulombFormCore_exists_norm_error N (hβ n) (u n)
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  have herr := fun n => coulombFormCore_error_components N (hβ n) (u n) (φ n) (hφ n)
  have hnorm : Tendsto (fun n => ‖coulombFormCore (hβ n) (φ n)‖) atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.norm_eq_abs, abs_abs, hu] using
      (abs_norm_sub_norm_le (coulombFormCore (hβ n) (φ n)) (u n)).trans (hφ n).le
  have hgradbound (n : ℕ) : ‖coulombFormGradientL N (hβ n)
      (coulombFormCore (hβ n) (φ n))‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    have ht := norm_add_le
      (coulombFormGradientL N (hβ n) (coulombFormCore (hβ n) (φ n)) -
        coulombFormGradientL N (hβ n) (u n))
      (coulombFormGradientL N (hβ n) (u n))
    rw [sub_add_cancel] at ht
    linarith [(herr n).2, hg n]
  have hgrad : Tendsto (fun n => ‖coulombFormGradientL N (hβ n)
      (coulombFormCore (hβ n) (φ n))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) hgradbound
    have hh : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero] using hh.const_mul (2 : ℝ)
  have hmean : Tendsto (fun n => poleBranchRealMean N (hβ n)
      (coulombFormValueL N (hβ n) (coulombFormCore (hβ n) (φ n)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [hm, sub_zero, Real.norm_eq_abs] using
      (coulombFormMean_error_le N (hβ n) (coulombFormCore (hβ n) (φ n)) (u n)).trans
        (hφ n).le
  exact ⟨φ, hφ, hnorm, hgrad, hmean⟩

theorem coulombTemperature_core_mass_energy {N : ℕ} (β : ℕ → ℝ)
    (hβ : ∀ n, 0 < β n) (φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤)
    (hnorm : Tendsto (fun n => ‖coulombFormCore (hβ n) (φ n)‖) atTop (𝓝 1))
    (hgrad : Tendsto (fun n => ‖coulombFormGradientL N (hβ n)
      (coulombFormCore (hβ n) (φ n))‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, φ n z ^ 2 ∂coulombMeasure N (β n)) atTop (𝓝 1) ∧
    Tendsto (fun n => ∫ z, ‖gradient (φ n : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N (β n)) atTop (𝓝 0) := by
  have heq (n : ℕ) : (∫ z, ‖gradient (φ n : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N (β n)) =
      ‖coulombFormGradientL N (hβ n) (coulombFormCore (hβ n) (φ n))‖ ^ 2 := by
    rw [← coulombFormCore_energy_eq_integral (hβ n) (φ n)]
    rfl
  have hmass (n : ℕ) : (∫ z, φ n z ^ 2 ∂coulombMeasure N (β n)) =
      ‖coulombFormCore (hβ n) (φ n)‖ ^ 2 -
      ‖coulombFormGradientL N (hβ n) (coulombFormCore (hβ n) (φ n))‖ ^ 2 := by
    have h := coulombFormCore_norm_sq_eq_integrals (hβ n) (φ n)
    rw [heq n] at h
    linarith only [h]
  constructor
  · simpa only [hmass, one_pow, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      (hnorm.pow 2).sub (hgrad.pow 2)
  · simpa only [heq, zero_pow (by decide : 2 ≠ 0)] using hgrad.pow 2

end RepulsiveCoulomb
