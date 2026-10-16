module

public import LeanResearch.RepulsiveCoulomb.SmoothDyadicTruncation
public import LeanResearch.RepulsiveCoulomb.PointConditionalPhysicalPoincare

@[expose] public section

/-! Physical Euclidean gradient control for genuine smooth truncations. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem smoothTruncation_comp_contDiff (a : ℝ) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun z => smoothDyadicTruncation a (f z)) :=
  ((smoothDyadicTruncation_contDiff a).of_le (by simp)).comp hf

theorem smoothTruncation_gradient_bound {a K : ℝ} (ha : 0 < a)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℂ) :
    ‖gradient (fun z => smoothDyadicTruncation a (f z)) x‖ ≤ K * ‖gradient f x‖ := by
  simp only [TauCeti.norm_gradient_eq_norm_fderiv]
  have ht : Differentiable ℝ (smoothDyadicTruncation a) :=
    (smoothDyadicTruncation_contDiff a).differentiable (by simp)
  change ‖fderiv ℝ (smoothDyadicTruncation a ∘ f) x‖ ≤ _
  rw [fderiv_comp x (ht (f x)) (hf.differentiable_one x)]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← norm_deriv_eq_norm_fderiv, smoothDyadicTruncation_deriv ha (f x)]
  exact hK _

theorem smoothTruncation_gradient_zero_outside {a : ℝ} (ha : 0 < a)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {x : ℂ} (hx : f x ∉ Ioo a (2 * a)) :
    gradient (fun z => smoothDyadicTruncation a (f z)) x = 0 := by
  apply norm_eq_zero.mp
  rw [TauCeti.norm_gradient_eq_norm_fderiv]
  have ht : Differentiable ℝ (smoothDyadicTruncation a) :=
    (smoothDyadicTruncation_contDiff a).differentiable (by simp)
  change ‖fderiv ℝ (smoothDyadicTruncation a ∘ f) x‖ = 0
  rw [fderiv_comp x (ht (f x)) (hf.differentiable_one x)]
  have he : fderiv ℝ (smoothDyadicTruncation a) (f x) = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_deriv_eq_norm_fderiv, smoothDyadicTruncation_deriv_zero_outside ha hx, norm_zero]
  rw [he, ContinuousLinearMap.zero_comp, norm_zero]

theorem smoothTruncation_gradient_energy_indicator {a K : ℝ} (ha : 0 < a) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℂ) :
    ‖gradient (fun z => smoothDyadicTruncation a (f z)) x‖ ^ 2 ≤
      {z | a < f z ∧ f z < 2 * a}.indicator (fun z => K ^ 2 * ‖gradient f z‖ ^ 2) x := by
  by_cases hx : x ∈ {z | a < f z ∧ f z < 2 * a}
  · rw [Set.indicator_of_mem hx]
    have h := smoothTruncation_gradient_bound ha hK hf x
    have hp : 0 ≤ K * ‖gradient f x‖ := mul_nonneg hK0 (norm_nonneg _)
    nlinarith [norm_nonneg (gradient (fun z => smoothDyadicTruncation a (f z)) x)]
  · rw [Set.indicator_of_notMem hx, smoothTruncation_gradient_zero_outside ha hf hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]

end RepulsiveCoulomb
