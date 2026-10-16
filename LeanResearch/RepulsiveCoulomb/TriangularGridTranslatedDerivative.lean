import LeanResearch.RepulsiveCoulomb.CompactC1GridControl
import LeanResearch.RepulsiveCoulomb.TriangularGridRegularPoints

/-! Explicit physical derivatives in every translated open grid triangle and
in the actual sampled mesh interpolant. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def gridTriangleDX (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) : ℝ :=
  if i.2 then v (i.1+(1,1)) - v (i.1+(0,1)) else v (i.1+(1,0)) - v i.1

def gridTriangleDY (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) : ℝ :=
  if i.2 then v (i.1+(0,1)) - v i.1 else v (i.1+(1,1)) - v (i.1+(1,0))

def gridTriangleDerivative (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) : ℂ →L[ℝ] ℝ :=
  gridTriangleDX v i • Complex.reCLM + gridTriangleDY v i • Complex.imCLM

theorem gridTriangleDerivative_one (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) :
    gridTriangleDerivative v i 1 = gridTriangleDX v i := by simp [gridTriangleDerivative]

theorem gridTriangleDerivative_I (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) :
    gridTriangleDerivative v i Complex.I = gridTriangleDY v i := by simp [gridTriangleDerivative]

theorem gridTriangleAffine_eq_const_add_derivative (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) (z : ℂ) :
    gridTriangleAffine v i z = gridTriangleAffine v i 0 + gridTriangleDerivative v i z := by
  rcases i with ⟨b,k⟩
  cases k <;> simp [gridTriangleAffine,gridLowerAffine_apply,gridUpperAffine_apply,
    gridTriangleDerivative,gridTriangleDX,gridTriangleDY] <;> ring

theorem gridOpenTriangle_isOpen (i : GridTriangle) : IsOpen (gridOpenTriangle i) := by
  rcases i with ⟨b,k⟩
  have hr : Continuous (fun z : ℂ => z.re - (b.1 : ℝ)) := Complex.continuous_re.sub continuous_const
  have hi : Continuous (fun z : ℂ => z.im - (b.2 : ℝ)) := Complex.continuous_im.sub continuous_const
  cases k
  · exact (isOpen_lt continuous_const hi).inter ((isOpen_lt hi hr).inter (isOpen_lt hr continuous_const))
  · exact (isOpen_lt continuous_const hr).inter ((isOpen_lt hr hi).inter (isOpen_lt hi continuous_const))

theorem gridTriangle_interpolant_hasFDerivAt (v : (ℤ × ℤ) →₀ ℝ) {i : GridTriangle} {z : ℂ}
    (hz : z ∈ gridOpenTriangle i) : HasFDerivAt (triangularGridInterpolant v) (gridTriangleDerivative v i) z := by
  have hloc : triangularGridInterpolant v =ᶠ[𝓝 z]
      (fun w => gridTriangleAffine v i 0 + gridTriangleDerivative v i w) := by
    filter_upwards [(gridOpenTriangle_isOpen i).mem_nhds hz] with w hw
    exact (gridTriangle_interpolant_eq_affine v (gridOpenTriangle_subset_region i hw)).trans
      (gridTriangleAffine_eq_const_add_derivative v i w)
  exact ((gridTriangleDerivative v i).hasFDerivAt.const_add (gridTriangleAffine v i 0)).congr_of_eventuallyEq hloc

theorem sampledGridApproximation_fderiv (f : ℂ → ℝ) (hc : HasCompactSupport f)
    (h : ℝ) (hh : 0 < h) {i : GridTriangle} {z : ℂ} (hz : h⁻¹ • z ∈ gridOpenTriangle i) :
    fderiv ℝ (sampledGridApproximation f hc h hh) z =
      h⁻¹ • gridTriangleDerivative (compactGridSamples f hc h hh) i := by
  unfold sampledGridApproximation scaledTriangularGridInterpolant
  rw [fderiv_comp_smul, (gridTriangle_interpolant_hasFDerivAt _ hz).fderiv]

end RepulsiveCoulomb
