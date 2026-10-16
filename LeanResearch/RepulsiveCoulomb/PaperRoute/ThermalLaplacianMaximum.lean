import LeanResearch.RepulsiveCoulomb.PaperRoute.LogFundamentalSolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv

/-! A genuine second-order maximum test.
Positive second derivative would imply strict local convexity and contradict
the midpoint inequality at a global maximum. No maximum-principle or
Laplacian-sign certificate is an input. -/
noncomputable section
open Real Set Metric Filter InnerProductSpace
open scoped Topology ContDiff
namespace RepulsiveCoulomb.PaperRoute

theorem deriv_deriv_nonpos_at_globalMax_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hmax : ∀ t : ℝ, f t ≤ f 0) :
    deriv (deriv f) 0 ≤ 0 := by
  by_contra hnot
  have hp : 0 < deriv (deriv f) 0 := lt_of_not_ge hnot
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hc : Continuous (deriv (deriv f)) := hd.continuous_deriv_one
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < deriv (deriv f) t :=
    hc.continuousAt.eventually (Ioi_mem_nhds hp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  have hpos : ∀ t ∈ Ioo (-ε) ε, 0 < deriv (deriv f) t := by
    intro t ht
    apply hball
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ht
  have hcv : StrictConvexOn ℝ (Ioo (-ε) ε) f :=
    strictConvexOn_of_deriv2_pos (convex_Ioo _ _) hf.continuous.continuousOn
      (fun t ht => by
        change 0 < deriv (deriv f) t
        exact hpos t (interior_subset ht))
  have hm : -ε/2 ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  have hp' : ε/2 ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  have hne : -ε/2 ≠ ε/2 := by linarith
  have hstrict := hcv.2 hm hp' hne (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have hmid : (1/2 : ℝ)*(-ε/2)+(1/2 : ℝ)*(ε/2)=0 := by ring
  simp only [smul_eq_mul, hmid] at hstrict
  linarith [hmax (-ε/2), hmax (ε/2)]

/-- A real line restriction transfers the actual scalar second-order test
to a physical planar Hessian entry. -/
theorem second_fderiv_nonpos_at_globalMax {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (x : ℂ) (hmax : ∀ y : ℂ, f y ≤ f x) (v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v ≤ 0 := by
  let c : ℝ → ℂ := fun t => x+t • v
  let g : ℝ → ℝ := f ∘ c
  have hc (t : ℝ) : HasDerivAt c v t := by
    convert ((hasDerivAt_id t).smul_const v).const_add x using 1 <;> simp [c]
  have hgc : ContDiff ℝ 2 g :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgm : ∀ t : ℝ, g t ≤ g 0 := by
    intro t
    simpa only [g, c, Function.comp_def, zero_smul, add_zero] using hmax (c t)
  have hfirst : deriv g = fun t => fderiv ℝ f (c t) v := by
    funext t
    exact ((hf.differentiable (by norm_num) (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)).deriv
  have hDv : ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hsecond : deriv (deriv g) 0 = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
    rw [hfirst]
    have h := ((hDv.differentiable (by norm_num) (c 0)).hasFDerivAt.comp_hasDerivAt 0 (hc 0)).deriv
    simpa only [c, zero_smul, add_zero, Function.comp_def] using h
  rw [← hsecond]
  exact deriv_deriv_nonpos_at_globalMax_zero hgc hgm

theorem laplacian_nonpos_at_globalMax {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (x : ℂ) (hmax : ∀ y : ℂ, f y ≤ f x) :
    Laplacian.laplacian f x ≤ 0 := by
  rw [laplacian_eq_second_fderiv hf]
  exact add_nonpos (second_fderiv_nonpos_at_globalMax hf x hmax 1)
    (second_fderiv_nonpos_at_globalMax hf x hmax Complex.I)

end RepulsiveCoulomb.PaperRoute
