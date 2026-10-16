module

public import LeanResearch.RepulsiveCoulomb.TriangularGridDerivativeEdges

@[expose] public section

/-! Actual C1 derivative error on open mesh triangles. Only first-derivative
oscillation is used; there is no C2 or unproved approximation hypothesis. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem sampled_grid_difference_derivative_error {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℝ) (hh : 0 < h) {z : ℂ} (i : GridTriangle)
    (hz : h⁻¹ • z ∈ gridTriangleRegion i) (j k : Fin 3) (e : ℂ)
    (hstep : gridTriangleVertices i j - gridTriangleVertices i k = e) (he : ‖e‖ = 1)
    {ε : ℝ} (hdf : ∀ w ∈ closedBall z (2*h), ‖fderiv ℝ f w - fderiv ℝ f z‖ ≤ ε) :
    |h⁻¹ * (compactGridSamples f hc h hh (gridTriangleNodes i j) -
      compactGridSamples f hc h hh (gridTriangleNodes i k)) - fderiv ℝ f z e| ≤ ε := by
  have hx : h • gridTriangleVertices i k ∈ closedBall z (2*h) := scaled_gridTriangle_vertex_dist i k hh hz
  have hy : h • gridTriangleVertices i j ∈ closedBall z (2*h) := scaled_gridTriangle_vertex_dist i j hh hz
  have hrem := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (fun w (_ : w ∈ closedBall z (2*h)) => hf.differentiable (by norm_num) w)
    hdf (convex_closedBall z (2*h)) hx hy
  have hdelta : h • gridTriangleVertices i j - h • gridTriangleVertices i k = h • e := by
    rw [← smul_sub,hstep]
  rw [hdelta] at hrem
  simp only [map_smul,smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos hh,he,mul_one] at hrem
  apply normalized_difference_error hh
  rw [compactGridSamples_apply,compactGridSamples_apply]
  exact hrem

theorem sampledGridApproximation_fderiv_error {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℝ) (hh : 0 < h) {z : ℂ} {i : GridTriangle}
    (hz : h⁻¹ • z ∈ gridOpenTriangle i) {ε : ℝ}
    (hdf : ∀ w ∈ closedBall z (2*h), ‖fderiv ℝ f w - fderiv ℝ f z‖ ≤ ε) :
    ‖fderiv ℝ (sampledGridApproximation f hc h hh) z - fderiv ℝ f z‖ ≤ 2*ε := by
  have hreg := gridOpenTriangle_subset_region i hz
  have hx := sampled_grid_difference_derivative_error hf hc h hh i hreg 1
    (if i.2 then 2 else 0) 1 (gridTriangle_horizontal_step i) (by simp) hdf
  have hy := sampled_grid_difference_derivative_error hf hc h hh i hreg 2
    (if i.2 then 0 else 1) Complex.I (gridTriangle_vertical_step i) (by simp) hdf
  rw [← gridTriangleDX_nodes] at hx
  rw [← gridTriangleDY_nodes] at hy
  have h1 : |(fderiv ℝ (sampledGridApproximation f hc h hh) z - fderiv ℝ f z) 1| ≤ ε := by
    rw [ContinuousLinearMap.sub_apply,sampledGridApproximation_fderiv f hc h hh hz,
      ContinuousLinearMap.smul_apply,smul_eq_mul,gridTriangleDerivative_one]
    exact hx
  have hI : |(fderiv ℝ (sampledGridApproximation f hc h hh) z - fderiv ℝ f z) Complex.I| ≤ ε := by
    rw [ContinuousLinearMap.sub_apply,sampledGridApproximation_fderiv f hc h hh hz,
      ContinuousLinearMap.smul_apply,smul_eq_mul,gridTriangleDerivative_I]
    exact hy
  exact (complex_realLinear_norm_le _).trans (by linarith)

theorem sampledGridApproximation_gradient_error {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (h : ℝ) (hh : 0 < h) {z : ℂ} {i : GridTriangle}
    (hz : h⁻¹ • z ∈ gridOpenTriangle i) {ε : ℝ}
    (hdf : ∀ w ∈ closedBall z (2*h), ‖fderiv ℝ f w - fderiv ℝ f z‖ ≤ ε) :
    ‖gradient (sampledGridApproximation f hc h hh) z - gradient f z‖ ≤ 2*ε := by
  rw [complex_gradient_sub_norm]
  exact sampledGridApproximation_fderiv_error hf hc h hh hz hdf

end RepulsiveCoulomb
