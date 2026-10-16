module

public import LeanResearch.RepulsiveCoulomb.WeightedEvenPoleRemoval
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! A fixed Cauchy integral selects the weighted removable extension canonically.
The product-measure theorem uses actual weighted integrability, not a Laurent or
meromorphy assumption. Joint differentiability is a separate subsequent step. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def poleBranchCauchy (f : ℂ → ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(0, r), (z - w)⁻¹ • f z

theorem weighted_even_puncture_cauchy {f : ℂ → ℂ} {a R r : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}))
    (hi : IntegrableOn (fun z => ‖z‖ ^ a * ‖f z‖ ^ 2) (ball (0 : ℂ) R))
    (heven : ∀ z ∈ ball (0 : ℂ) R, f (-z) = f z) :
    DifferentiableOn ℂ (poleBranchCauchy f r) (ball (0 : ℂ) r) ∧
      ∀ z ∈ ball (0 : ℂ) r \ {0}, poleBranchCauchy f r z = f z := by
  obtain ⟨F, hF, hEq⟩ := weighted_even_puncture_removable ha ha2 (hr.trans hrR) hf hi heven
  have hcan : ∀ w ∈ ball (0 : ℂ) r, poleBranchCauchy f r w = F w := by
    intro w hw
    have hcircle : (∮ z in C(0, r), (z - w)⁻¹ • f z) =
        ∮ z in C(0, r), (z - w)⁻¹ • F z := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have hzR : z ∈ ball (0 : ℂ) R :=
        (closedBall_subset_ball hrR) (sphere_subset_closedBall hz)
      have hz0 : z ≠ 0 := by
        intro h
        subst z
        have hzero : (0 : ℝ) = r := by simpa only [mem_sphere, dist_self] using hz
        exact hr.ne' hzero.symm
      dsimp only
      rw [hEq z ⟨hzR, by simpa only [mem_singleton_iff] using hz0⟩]
    rw [poleBranchCauchy, hcircle,
      (hF.mono (closedBall_subset_ball hrR)).circleIntegral_sub_inv_smul hw,
      inv_smul_smul₀]
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(hF.mono (ball_subset_ball hrR.le)).congr hcan, ?_⟩
  intro z hz
  exact (hcan z hz.1).trans (hEq z ⟨ball_subset_ball hrR.le hz.1, hz.2⟩)

theorem weighted_even_puncture_cauchy_ae {P : Type*} [MeasurableSpace P]
    (μ : Measure P) [SFinite μ] {f : P × ℂ → ℂ} {a R r : ℝ}
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hr : 0 < r) (hrR : r < R)
    (hf : ∀ᵐ p ∂μ, DifferentiableOn ℂ (fun z => f (p, z)) (ball (0 : ℂ) R \ {0}))
    (hi : Integrable (fun pz : P × ℂ => ‖pz.2‖ ^ a * ‖f pz‖ ^ 2)
      (μ.prod (volume.restrict (ball (0 : ℂ) R))))
    (heven : ∀ᵐ p ∂μ, ∀ z ∈ ball (0 : ℂ) R, f (p, -z) = f (p, z)) :
    ∀ᵐ p ∂μ,
      DifferentiableOn ℂ (poleBranchCauchy (fun z => f (p, z)) r) (ball (0 : ℂ) r) ∧
        ∀ z ∈ ball (0 : ℂ) r \ {0}, poleBranchCauchy (fun z => f (p, z)) r z = f (p, z) := by
  filter_upwards [hi.prod_right_ae, hf, heven] with p hip hfp hep
  exact weighted_even_puncture_cauchy ha ha2 hr hrR hfp hip hep

end RepulsiveCoulomb
