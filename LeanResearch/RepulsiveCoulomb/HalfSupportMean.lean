import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison

/-! Correct centering of nonnegative truncations supported on at most half
the measure. This is the missing justification when using mean-centered weak
estimates in a median truncation argument. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem average_le_half_height_of_half_support {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    {S : Set X} (hS : MeasurableSet S) (hhalf : μ.real S ≤ μ.real univ / 2)
    {v : X → ℝ} (hv : Integrable v μ) {a : ℝ} (ha : 0 ≤ a)
    (hva : ∀ x, v x ≤ a) (hvzero : ∀ x ∉ S, v x = 0) :
    (⨍ x, v x ∂μ) ≤ a / 2 := by
  have hI : Integrable (S.indicator (fun _ : X => a)) μ := (integrable_const a).indicator hS
  have hpoint : ∀ x, v x ≤ S.indicator (fun _ : X => a) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact hva x
    · rw [Set.indicator_of_notMem hx, hvzero x hx]
  have h := integral_mono hv hI hpoint
  rw [integral_indicator hS, setIntegral_const, smul_eq_mul] at h
  have hmass : 0 < μ.real univ := measureReal_univ_pos
  rw [average_eq, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ hmass).mpr
  have hm := mul_le_mul_of_nonneg_right hhalf ha
  nlinarith

theorem half_height_lt_centered_on_plateau {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {v : X → ℝ} {a : ℝ} (ha : 0 < a)
    (hmean : (⨍ x, v x ∂μ) ≤ a / 2) {x : X} (hx : v x = a) :
    a / 4 < ‖v x - (⨍ z, v z ∂μ)‖ := by
  rw [hx, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

end RepulsiveCoulomb
