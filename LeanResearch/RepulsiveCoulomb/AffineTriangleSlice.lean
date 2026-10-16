import LeanResearch.RepulsiveCoulomb.TriangleSliceBarycentric
import Mathlib.Analysis.Convex.Combination

/-! Exact mixed-sign affine slice of a genuine three-vertex convex hull. -/
noncomputable section
open Set AffineMap
open scoped BigOperators
namespace RepulsiveCoulomb

theorem convexHull_three_barycentric {p₀ p₁ p₂ x : ℂ}
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂)
    (hx : x ∈ convexHull ℝ ({p₀, p₁, p₂} : Set ℂ)) :
    ∃ l₀ l₁ l₂ : ℝ, 0 ≤ l₀ ∧ 0 ≤ l₁ ∧ 0 ≤ l₂ ∧
      l₀ + l₁ + l₂ = 1 ∧ l₀ • p₀ + l₁ • p₁ + l₂ • p₂ = x := by
  classical
  have hx' : x ∈ convexHull ℝ (({p₀, p₁, p₂} : Finset ℂ) : Set ℂ) := by simpa using hx
  obtain ⟨w, hw, hsum, hpoint⟩ := Finset.mem_convexHull'.mp hx'
  refine ⟨w p₀, w p₁, w p₂, hw p₀ (by simp), hw p₁ (by simp), hw p₂ (by simp), ?_, ?_⟩
  · simpa [h01, h02, h12, add_assoc] using hsum
  · simpa [h01, h02, h12, add_assoc] using hpoint

theorem affineMap_apply_barycentric_three (f : ℂ →ᵃ[ℝ] ℝ) (p₀ p₁ p₂ : ℂ)
    {l₀ l₁ l₂ : ℝ} (hs : l₀ + l₁ + l₂ = 1) :
    f (l₀ • p₀ + l₁ • p₁ + l₂ • p₂) = l₀ * f p₀ + l₁ * f p₁ + l₂ * f p₂ := by
  let w : Fin 3 → ℝ := ![l₀, l₁, l₂]
  let p : Fin 3 → ℂ := ![p₀, p₁, p₂]
  have hw : ∑ i : Fin 3, w i = 1 := by simpa [w, Fin.sum_univ_succ, add_assoc] using hs
  have h := Finset.univ.map_affineCombination p w hw f
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
    Finset.affineCombination_eq_linear_combination _ _ _ hw] at h
  simpa [p, w, Fin.sum_univ_succ, smul_eq_mul, add_assoc] using h

theorem affine_triangle_zero_slice (f : ℂ →ᵃ[ℝ] ℝ) (p₀ p₁ p₂ : ℂ)
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂)
    (h0 : 0 < f p₀) (h1 : f p₁ < 0) (h2 : f p₂ < 0) :
    convexHull ℝ ({p₀, p₁, p₂} : Set ℂ) ∩ f ⁻¹' {0} =
      segment ℝ (affineLevelEdgePoint p₀ p₁ (f p₀) (f p₁) 0)
        (affineLevelEdgePoint p₀ p₂ (f p₀) (f p₂) 0) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨l₀, l₁, l₂, hl0, hl1, hl2, hls, hlx⟩ := convexHull_three_barycentric h01 h02 h12 hx.1
    have hf := affineMap_apply_barycentric_three f p₀ p₁ p₂ hls
    rw [hlx, show f x = 0 from hx.2] at hf
    rw [← hlx]
    exact barycentric_zero_mem_crossing_segment p₀ p₁ p₂ h0 h1 h2 hl0 hl1 hl2 hls hf.symm
  · have hc := (convex_convexHull ℝ ({p₀, p₁, p₂} : Set ℂ)).inter
      ((convex_singleton (0 : ℝ)).affine_preimage f)
    apply hc.segment_subset
    · refine ⟨?_, affineLevelEdgePoint_apply f p₀ p₁ (by linarith) 0⟩
      apply (convex_convexHull ℝ ({p₀, p₁, p₂} : Set ℂ)).segment_subset
        (subset_convexHull ℝ _ (by simp : p₀ ∈ ({p₀, p₁, p₂} : Set ℂ)))
        (subset_convexHull ℝ _ (by simp : p₁ ∈ ({p₀, p₁, p₂} : Set ℂ)))
      exact openSegment_subset_segment ℝ p₀ p₁ (affineLevelEdgePoint_mem_openSegment p₀ p₁ (Or.inr ⟨h1, h0⟩))
    · refine ⟨?_, affineLevelEdgePoint_apply f p₀ p₂ (by linarith) 0⟩
      apply (convex_convexHull ℝ ({p₀, p₁, p₂} : Set ℂ)).segment_subset
        (subset_convexHull ℝ _ (by simp : p₀ ∈ ({p₀, p₁, p₂} : Set ℂ)))
        (subset_convexHull ℝ _ (by simp : p₂ ∈ ({p₀, p₁, p₂} : Set ℂ)))
      exact openSegment_subset_segment ℝ p₀ p₂ (affineLevelEdgePoint_mem_openSegment p₀ p₂ (Or.inr ⟨h2, h0⟩))

end RepulsiveCoulomb
