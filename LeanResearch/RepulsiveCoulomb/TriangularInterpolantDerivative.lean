module

public import LeanResearch.RepulsiveCoulomb.TriangularInterpolantCell
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

/-! Actual physical Frechet derivatives of the finite interpolant in the open
triangles. No differentiability across grid edges is asserted. -/
noncomputable section
open Filter
open scoped Topology
namespace RepulsiveCoulomb

def gridLowerDerivative (v : (ℤ × ℤ) →₀ ℝ) : ℂ →L[ℝ] ℝ :=
  (v (1, 0) - v (0, 0)) • Complex.reCLM + (v (1, 1) - v (1, 0)) • Complex.imCLM

def gridUpperDerivative (v : (ℤ × ℤ) →₀ ℝ) : ℂ →L[ℝ] ℝ :=
  (v (1, 1) - v (0, 1)) • Complex.reCLM + (v (0, 1) - v (0, 0)) • Complex.imCLM

theorem triangularGridInterpolant_hasFDerivAt_lower (v : (ℤ × ℤ) →₀ ℝ) {z : ℂ}
    (hy : 0 < z.im) (hyx : z.im < z.re) (hx : z.re < 1) :
    HasFDerivAt (triangularGridInterpolant v) (gridLowerDerivative v) z := by
  have hloc : triangularGridInterpolant v =ᶠ[𝓝 z]
      (fun w => v (0, 0) + gridLowerDerivative v w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hy,
      (isOpen_lt Complex.continuous_im Complex.continuous_re).mem_nhds hyx,
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hx] with w hw0 hw1 hw2
    rw [triangularGridInterpolant_lower_cell v hw0.le hw1.le hw2.le]
    simp only [gridLowerDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
    ring
  exact (gridLowerDerivative v).hasFDerivAt.const_add (v (0, 0)) |>.congr_of_eventuallyEq hloc

theorem triangularGridInterpolant_hasFDerivAt_upper (v : (ℤ × ℤ) →₀ ℝ) {z : ℂ}
    (hx : 0 < z.re) (hxy : z.re < z.im) (hy : z.im < 1) :
    HasFDerivAt (triangularGridInterpolant v) (gridUpperDerivative v) z := by
  have hloc : triangularGridInterpolant v =ᶠ[𝓝 z]
      (fun w => v (0, 0) + gridUpperDerivative v w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx,
      (isOpen_lt Complex.continuous_re Complex.continuous_im).mem_nhds hxy,
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hy] with w hw0 hw1 hw2
    rw [triangularGridInterpolant_upper_cell v hw0.le hw1.le hw2.le]
    simp only [gridUpperDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
    ring
  exact (gridUpperDerivative v).hasFDerivAt.const_add (v (0, 0)) |>.congr_of_eventuallyEq hloc

end RepulsiveCoulomb
