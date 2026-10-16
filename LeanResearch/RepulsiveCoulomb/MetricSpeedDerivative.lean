import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Exact derivative norm from a local constant-speed distance identity. -/
open Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem norm_deriv_eq_of_local_scaled_dist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {x L : ℝ} (hf : DifferentiableAt ℝ f x)
    (h : ∀ᶠ y in 𝓝 x, dist (f y) (f x) = |y - x| * L) :
    ‖deriv f x‖ = L := by
  have ht := hf.hasDerivAt.tendsto_slope.norm
  have he : (fun y => ‖slope f x y‖) =ᶠ[𝓝[≠] x] (fun _ => L) := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hne
    have hyx : y ≠ x := by simpa using hne
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, ← dist_eq_norm, hy,
      ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr hyx)), one_mul]
  exact tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds

end RepulsiveCoulomb
