import LeanResearch.RepulsiveCoulomb.PointCoreCutoffProducts

/-! Joint physical energy control for a cutoff and its complement. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem physical_gradient_one_sub {χ : ℂ → ℝ} {z : ℂ}
    (hχ : DifferentiableAt ℝ χ z) :
    gradient (fun x => 1 - χ x) z = -gradient χ z := by
  apply (toDual ℝ ℂ).injective
  simp only [toDual_gradient, map_neg]
  rw [fderiv_fun_sub (differentiableAt_const 1) hχ]
  simp

theorem physical_product_gradient_sq_le {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    ‖gradient (fun x => f x * g x) z‖ ^ 2 ≤
      2 * f z ^ 2 * ‖gradient g z‖ ^ 2 + 2 * g z ^ 2 * ‖gradient f z‖ ^ 2 := by
  rw [physical_gradient_mul hf hg]
  have ht := norm_add_le (f z • gradient g z) (g z • gradient f z)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at ht
  have hs := mul_self_le_mul_self (norm_nonneg _) ht
  have hy := sq_nonneg (|f z| * ‖gradient g z‖ - |g z| * ‖gradient f z‖)
  nlinarith [sq_abs (f z), sq_abs (g z)]

theorem cutoff_pair_gradient_sq_le {χ f : ℂ → ℝ} {z : ℂ} {D : ℝ}
    (hχ : DifferentiableAt ℝ χ z) (hf : DifferentiableAt ℝ f z)
    (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1) (hD : 0 ≤ D)
    (hb : ‖gradient χ z‖ ≤ D) :
    ‖gradient (fun x => χ x * f x) z‖ ^ 2 +
      ‖gradient (fun x => (1 - χ x) * f x) z‖ ^ 2 ≤
      2 * ‖gradient f z‖ ^ 2 + 4 * D ^ 2 * f z ^ 2 := by
  have hi := physical_product_gradient_sq_le hχ hf
  have ho := physical_product_gradient_sq_le ((differentiableAt_const 1).sub hχ) hf
  change ‖gradient (fun x => (1 - χ x) * f x) z‖ ^ 2 ≤
    2 * (1 - χ z) ^ 2 * ‖gradient f z‖ ^ 2 + 2 * f z ^ 2 * ‖gradient (fun x => 1 - χ x) z‖ ^ 2 at ho
  rw [physical_gradient_one_sub hχ, norm_neg] at ho
  have hc : χ z ^ 2 + (1 - χ z) ^ 2 ≤ 1 := by nlinarith
  have hbs : ‖gradient χ z‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (gradient χ z)]
  have hcE := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖gradient f z‖)
  have hbF := mul_le_mul_of_nonneg_right hbs (sq_nonneg (f z))
  nlinarith

theorem cutoff_pair_energy_le {χ f : ℂ → ℝ} {D : ℝ} (μ : Measure ℂ)
    (hχ : Differentiable ℝ χ) (hf : Differentiable ℝ f)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ z, ‖gradient χ z‖ ≤ D)
    (hi : Integrable (fun x => ‖gradient (fun z => χ z * f z) x‖ ^ 2) μ)
    (ho : Integrable (fun x => ‖gradient (fun z => (1 - χ z) * f z) x‖ ^ 2) μ)
    (he : Integrable (fun x => ‖gradient f x‖ ^ 2) μ)
    (hm : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, ‖gradient (fun z => χ z * f z) x‖ ^ 2 ∂μ) +
      (∫ x, ‖gradient (fun z => (1 - χ z) * f z) x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖gradient f x‖ ^ 2 ∂μ) + 4 * D ^ 2 * (∫ x, f x ^ 2 ∂μ) := by
  rw [← integral_add hi ho, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (he.const_mul 2) (hm.const_mul (4 * D ^ 2))]
  exact integral_mono (hi.add ho) ((he.const_mul 2).add (hm.const_mul (4 * D ^ 2)))
    (fun x => cutoff_pair_gradient_sq_le (hχ x) (hf x) (hχ0 x) (hχ1 x) hD (hb x))

end RepulsiveCoulomb
