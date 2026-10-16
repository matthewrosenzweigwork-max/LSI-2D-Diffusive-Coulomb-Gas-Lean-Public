import LeanResearch.RepulsiveCoulomb.PointCoreEntropyLayer

/-! Zero-safe entropy and physical energy scaling for core normalization. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb

theorem mul_log_product (x y : ℝ) :
    (x * y) * Real.log (x * y) = y * (x * Real.log x) + x * (y * Real.log y) := by
  have h := Real.negMulLog_mul x y
  unfold Real.negMulLog at h
  nlinarith only [h]

theorem bounded_squareEntropy_smul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) (c : ℝ) :
    Rothaus.squareEntropy μ (fun x => c * f x) = c ^ 2 * Rothaus.squareEntropy μ f := by
  have hi : Integrable (fun x => f x ^ 2) μ :=
    Rothaus.integrable_continuous_comp_bounded hf hb (continuous_id.pow 2)
  have hl : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    Rothaus.integrable_continuous_comp_bounded hf hb (Real.continuous_mul_log.comp (continuous_id.pow 2))
  have hmass : (∫ x, (c * f x) ^ 2 ∂μ) = c ^ 2 * (∫ x, f x ^ 2 ∂μ) := by
    simp only [mul_pow, integral_const_mul]
  have hlog : (∫ x, (c * f x) ^ 2 * Real.log ((c * f x) ^ 2) ∂μ) =
      (∫ x, f x ^ 2 ∂μ) * (c ^ 2 * Real.log (c ^ 2)) +
        c ^ 2 * (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) := by
    simp_rw [mul_pow, mul_log_product]
    rw [integral_add (hi.mul_const _) (hl.const_mul _), integral_mul_const, integral_const_mul]
  unfold Rothaus.squareEntropy
  rw [hmass, hlog, mul_log_product]
  ring

theorem testFunction_smul_mass (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (μ : Measure ℂ) (c : ℝ) :
    (∫ x, (c • φ : TestFunction Ω ℝ ⊤) x ^ 2 ∂μ) = c ^ 2 * (∫ x, φ x ^ 2 ∂μ) := by
  change (∫ x, (c * φ x) ^ 2 ∂μ) = _
  simp only [mul_pow, integral_const_mul]

theorem testFunction_smul_energy (Ω : TopologicalSpace.Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (μ : Measure ℂ) (c : ℝ) :
    (∫ x, ‖gradient (c • φ : TestFunction Ω ℝ ⊤) x‖ ^ 2 ∂μ) =
      c ^ 2 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have h := TauCeti.gradient_const_smul (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) (x := x) c
  have hn := congrArg (fun v : ℂ => ‖v‖ ^ 2) h
  simpa [norm_smul, mul_pow] using hn

end RepulsiveCoulomb
