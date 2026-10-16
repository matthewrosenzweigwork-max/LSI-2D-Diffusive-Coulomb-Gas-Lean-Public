import LeanResearch.RepulsiveCoulomb.ComplexDerivativeComponents

/-! The horizontal and vertical sample differences used by the actual triangle
derivative, with physical edge increments and distance bounds. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem gridTriangleDX_nodes (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) :
    gridTriangleDX v i = v (gridTriangleNodes i 1) - v (gridTriangleNodes i (if i.2 then 2 else 0)) := by
  rcases i with ⟨b,k⟩
  cases k <;> simp [gridTriangleDX,gridTriangleNodes]

theorem gridTriangleDY_nodes (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle) :
    gridTriangleDY v i = v (gridTriangleNodes i 2) - v (gridTriangleNodes i (if i.2 then 0 else 1)) := by
  rcases i with ⟨b,k⟩
  cases k <;> simp [gridTriangleDY,gridTriangleNodes]

theorem gridTriangle_horizontal_step (i : GridTriangle) :
    gridTriangleVertices i 1 - gridTriangleVertices i (if i.2 then 2 else 0) = (1 : ℂ) := by
  rcases i with ⟨⟨x,y⟩,k⟩
  cases k <;> apply Complex.ext <;> simp [gridTriangleVertices,gridTriangleNodes,complexLatticePoint]

theorem gridTriangle_vertical_step (i : GridTriangle) :
    gridTriangleVertices i 2 - gridTriangleVertices i (if i.2 then 0 else 1) = Complex.I := by
  rcases i with ⟨⟨x,y⟩,k⟩
  cases k <;> apply Complex.ext <;> simp [gridTriangleVertices,gridTriangleNodes,complexLatticePoint]

theorem scaled_gridTriangle_vertex_dist (i : GridTriangle) (j : Fin 3)
    {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : h⁻¹ • z ∈ gridTriangleRegion i) :
    dist (h • gridTriangleVertices i j) z ≤ 2*h := by
  have hd := gridTriangleRegion_dist_le_two (gridTriangleVertices_mem_region i j) hz
  have he : h • (h⁻¹ • z) = z := by rw [smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  calc
    _ = dist (h • gridTriangleVertices i j) (h • (h⁻¹ • z)) := by rw [he]
    _ = h * dist (gridTriangleVertices i j) (h⁻¹ • z) := by rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hh]
    _ ≤ h*2 := mul_le_mul_of_nonneg_left hd hh.le
    _ = _ := by ring

end RepulsiveCoulomb
