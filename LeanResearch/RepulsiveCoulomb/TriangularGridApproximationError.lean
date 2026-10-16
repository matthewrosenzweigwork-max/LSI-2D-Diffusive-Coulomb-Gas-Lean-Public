module

public import LeanResearch.RepulsiveCoulomb.TriangularGridSampling

@[expose] public section

/-! Actual uniform value error for the sampled finite-grid interpolant. -/
noncomputable section
open Set Metric
open scoped NNReal
namespace RepulsiveCoulomb

theorem gridTriangle_interpolant_eq_affine (v : (ℤ × ℤ) →₀ ℝ) {i : GridTriangle} {z : ℂ}
    (hz : z ∈ gridTriangleRegion i) : triangularGridInterpolant v z = gridTriangleAffine v i z := by
  rcases i with ⟨b,k⟩
  cases k
  · exact triangularGridInterpolant_eq_lowerAffine v b hz
  · exact triangularGridInterpolant_eq_upperAffine v b hz

theorem gridTriangleVertices_mem_region (i : GridTriangle) (j : Fin 3) :
    gridTriangleVertices i j ∈ gridTriangleRegion i := by
  rw [gridTriangleRegion_convexHull]
  exact subset_convexHull ℝ _ (mem_range_self j)

theorem exists_gridTriangleRegion (z : ℂ) : ∃ i : GridTriangle, z ∈ gridTriangleRegion i := by
  obtain ⟨b,hb⟩ := exists_grid_triangle z
  rcases hb with h | h
  · exact ⟨(b,false),h⟩
  · exact ⟨(b,true),h⟩

theorem gridTriangle_interpolant_abs_le (v : (ℤ × ℤ) →₀ ℝ) (i : GridTriangle)
    {z : ℂ} (hz : z ∈ gridTriangleRegion i) (L ε : ℝ)
    (hval : ∀ j : Fin 3, |v (gridTriangleNodes i j) - L| ≤ ε) :
    |triangularGridInterpolant v z - L| ≤ ε := by
  have hsub : convexHull ℝ (range (gridTriangleVertices i)) ⊆
      (gridTriangleAffine v i) ⁻¹' Icc (L-ε) (L+ε) := by
    apply convexHull_min ?_ ((convex_Icc (L-ε) (L+ε)).affine_preimage (gridTriangleAffine v i))
    rintro w ⟨j,rfl⟩
    change L-ε ≤ gridTriangleAffine v i (gridTriangleVertices i j) ∧
      gridTriangleAffine v i (gridTriangleVertices i j) ≤ L+ε
    rw [gridTriangleAffine_vertex_values]
    have hh := abs_le.mp (hval j)
    constructor <;> linarith [hh.1,hh.2]
  have hh := hsub ((gridTriangleRegion_convexHull i) ▸ hz)
  change L-ε ≤ gridTriangleAffine v i z ∧ gridTriangleAffine v i z ≤ L+ε at hh
  rw [← gridTriangle_interpolant_eq_affine v hz] at hh
  apply abs_le.mpr
  constructor <;> linarith [hh.1,hh.2]

theorem sampledGridApproximation_abs_error {f : ℂ → ℝ} (hf : HasCompactSupport f)
    {C : ℝ≥0} (hL : LipschitzWith C f) (h : ℝ) (hh : 0 < h) (z : ℂ) :
    |sampledGridApproximation f hf h hh z - f z| ≤ 2 * (C : ℝ) * h := by
  obtain ⟨i,hi⟩ := exists_gridTriangleRegion (h⁻¹ • z)
  unfold sampledGridApproximation scaledTriangularGridInterpolant
  apply gridTriangle_interpolant_abs_le _ i hi
  intro j
  rw [compactGridSamples_apply]
  change |f (h • gridTriangleVertices i j) - f z| ≤ _
  have hd := gridTriangleRegion_dist_le_two (gridTriangleVertices_mem_region i j) hi
  have he : h • (h⁻¹ • z) = z := by rw [smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  have hdist : dist (h • gridTriangleVertices i j) z ≤ h * 2 := by
    calc
      _ = dist (h • gridTriangleVertices i j) (h • (h⁻¹ • z)) := by rw [he]
      _ = h * dist (gridTriangleVertices i j) (h⁻¹ • z) := by
        rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hh]
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hh.le
  have hp := (hL.dist_le_mul (h • gridTriangleVertices i j) z).trans
    (mul_le_mul_of_nonneg_left hdist C.coe_nonneg)
  rw [Real.dist_eq] at hp
  nlinarith

end RepulsiveCoulomb
