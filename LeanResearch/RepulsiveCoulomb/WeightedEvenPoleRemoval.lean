import LeanResearch.RepulsiveCoulomb.WeightedPunctureVanishing
import Mathlib.Analysis.Complex.RemovableSingularity

/-! Weighted L2 and evenness remove the puncture, including the endpoint exponent two. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem weighted_holomorphic_linear_pole_extension {f : ℂ → ℂ} {a R : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}))
    (hi : IntegrableOn (fun z => ‖z‖ ^ a * ‖f z‖ ^ 2) (ball (0 : ℂ) R)) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball (0 : ℂ) R) ∧
      ∀ z ∈ ball (0 : ℂ) R \ {0}, H z = z * f z := by
  let g : ℂ → ℂ := fun z => z * f z
  have hg : DifferentiableOn ℂ g (ball (0 : ℂ) R \ {0}) := differentiableOn_id.mul hf
  have ho : (fun z => g z - g 0) =o[𝓝[≠] (0 : ℂ)] (fun z => (z - 0)⁻¹) := by
    have hzfun : ∀ z : ℂ, (z - 0)⁻¹ = 0 → g z - g 0 = 0 := by
      intro z hz
      have hz0 : z = 0 := by simpa only [sub_zero] using inv_eq_zero.mp hz
      simp only [hz0, sub_self]
    apply (Asymptotics.isLittleO_iff_tendsto hzfun).mpr
    have h : Tendsto (fun z : ℂ => z ^ 2 * f z) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      (weighted_holomorphic_square_pole_tendsto ha ha2 hR hf hi).mono_left nhdsWithin_le_nhds
    convert h using 1
    funext z
    simp only [g, zero_mul, sub_zero, div_inv_eq_mul]
    ring

  let H := Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g)
  refine ⟨H, Complex.differentiableOn_update_limUnder_of_isLittleO (ball_mem_nhds _ hR) hg ho, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := by simpa only [mem_singleton_iff] using hz.2
  simp only [H, Function.update_of_ne hz0, g]

theorem continuous_odd_puncture_extension_zero {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hH : ContinuousAt H 0)
    (hodd : ∀ z ∈ ball (0 : ℂ) R \ {0}, H (-z) = -H z) : H 0 = 0 := by
  have hn : Tendsto (fun z : ℂ => -z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun z : ℂ => H (-z)) (𝓝[≠] (0 : ℂ)) (𝓝 (H 0)) := hH.tendsto.comp hn
  have hr : Tendsto (fun z : ℂ => -H z) (𝓝[≠] (0 : ℂ)) (𝓝 (-H 0)) :=
    (hH.tendsto.mono_left nhdsWithin_le_nhds).neg
  have hb0 : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) R := ball_mem_nhds _ hR
  have hb : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∈ ball (0 : ℂ) R :=
    hb0.filter_mono nhdsWithin_le_nhds
  have he : (fun z : ℂ => H (-z)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => -H z) := by
    filter_upwards [self_mem_nhdsWithin, hb] with z hz hzr
    exact hodd z ⟨hzr, hz⟩
  have hz := tendsto_nhds_unique hl (hr.congr' he.symm)
  linear_combination (1 / 2 : ℂ) * hz

theorem weighted_even_puncture_removable {f : ℂ → ℂ} {a R : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}))
    (hi : IntegrableOn (fun z => ‖z‖ ^ a * ‖f z‖ ^ 2) (ball (0 : ℂ) R))
    (heven : ∀ z ∈ ball (0 : ℂ) R, f (-z) = f z) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (0 : ℂ) R) ∧
      ∀ z ∈ ball (0 : ℂ) R \ {0}, F z = f z := by
  obtain ⟨H,hH,hEq⟩ := weighted_holomorphic_linear_pole_extension ha ha2 hR hf hi
  have hc : ContinuousAt H 0 := hH.continuousOn.continuousAt (ball_mem_nhds _ hR)
  have h0 : H 0 = 0 := continuous_odd_puncture_extension_zero hR hc (by
    intro z hz
    have hn : -z ∈ ball (0 : ℂ) R \ {0} := by
      constructor
      · simpa only [mem_ball, dist_zero_right, norm_neg] using hz.1
      · simpa only [mem_singleton_iff, neg_eq_zero] using hz.2
    rw [hEq (-z) hn, hEq z hz, heven z hz.1, neg_mul])
  refine ⟨dslope H 0, (Complex.differentiableOn_dslope (ball_mem_nhds _ hR)).mpr hH, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := by simpa only [mem_singleton_iff] using hz.2
  rw [dslope_of_ne H hz0, slope_def_field, h0, hEq z hz, sub_zero, sub_zero]
  exact mul_div_cancel_left₀ (f z) hz0

end RepulsiveCoulomb
