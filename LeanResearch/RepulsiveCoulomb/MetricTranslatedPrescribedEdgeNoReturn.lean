module

public import LeanResearch.RepulsiveCoulomb.ComplexBoundarySideRigidity
public import LeanResearch.RepulsiveCoulomb.TranslatedSupportingHalfplane

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Exclude returns to either prescribed straight
old edge by two distances. This covers an actual halfline or a finite edge,
without extending either one to a fictitious complete old boundary line.
The remaining forward-boundary return is deliberately NOT asserted here.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- An actual flat patch cannot meet the same minimizing straight edge away
from its Euclidean supporting line. The target may be any metric space. -/
theorem metric_flat_patch_no_prescribed_edge_return {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} {S : Set ℝ}
    (ρ : S → Y) (hρ : Isometry ρ) (F : K → Y) (hF : Isometry F)
    (E : ℂ ≃ᵢ ℂ) (c d : S) (hcd : c.1 ≠ d.1) (x₀ x₁ : K)
    (hc : E x₀.1 = (c.1 : ℂ)) (hd : E x₁.1 = (d.1 : ℂ))
    (hFc : F x₀ = ρ c) (hFd : F x₁ = ρ d)
    (z : K) (hz : (E z.1).im ≠ 0) : F z ∉ range ρ := by
  rintro ⟨q, hq⟩
  have hreal (s t : ℝ) : dist (s : ℂ) (t : ℂ) = dist s t := by
    simp only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Real.dist_eq]
  have hdistc : dist (E z.1) (c.1 : ℂ) = dist (q.1 : ℂ) (c.1 : ℂ) := by
    rw [hreal, ← hc, E.dist_eq]
    have h := hF.dist_eq z x₀
    rw [hFc, ← hq, hρ.dist_eq] at h
    exact h.symm
  have hdistd : dist (E z.1) (d.1 : ℂ) = dist (q.1 : ℂ) (d.1 : ℂ) := by
    rw [hreal, ← hd, E.dist_eq]
    have h := hF.dist_eq z x₁
    rw [hFd, ← hq, hρ.dist_eq] at h
    exact h.symm
  rcases complex_eq_or_conj_of_two_real_dist_eq hcd hdistc hdistd with he | he
  · apply hz
    simpa only [Complex.ofReal_im] using congrArg Complex.im he
  · apply hz
    simpa only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_im] using congrArg Complex.im he

end RepulsiveCoulomb
