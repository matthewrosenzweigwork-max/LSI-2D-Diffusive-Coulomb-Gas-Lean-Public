module

public import LeanResearch.RepulsiveCoulomb.AffineTriangleSlice

@[expose] public section

/-! Threshold and orientation invariant triangle slices from two genuine incident
edge crossings. No affine formula is assumed to be globally shared by cells. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

theorem levelEdgeParameter_shift (u v t : ℝ) :
    levelEdgeParameter (u - t) (v - t) 0 = levelEdgeParameter u v t := by
  unfold levelEdgeParameter
  congr 1 <;> ring

theorem levelEdgeParameter_neg (u v t : ℝ) :
    levelEdgeParameter (-u) (-v) (-t) = levelEdgeParameter u v t := by
  unfold levelEdgeParameter
  rw [show -t - -u = -(t - u) by ring, show -v - -u = -(v - u) by ring, neg_div_neg_eq]

theorem affine_triangle_level_slice_high (f : ℂ →ᵃ[ℝ] ℝ) (p₀ p₁ p₂ : ℂ)
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) {t : ℝ}
    (h0 : t < f p₀) (h1 : f p₁ < t) (h2 : f p₂ < t) :
    convexHull ℝ ({p₀, p₁, p₂} : Set ℂ) ∩ f ⁻¹' {t} =
      segment ℝ (affineLevelEdgePoint p₀ p₁ (f p₀) (f p₁) t)
        (affineLevelEdgePoint p₀ p₂ (f p₀) (f p₂) t) := by
  let g := f - AffineMap.const ℝ ℂ t
  have hg (z : ℂ) : g z = f z - t := rfl
  have h := affine_triangle_zero_slice g p₀ p₁ p₂ h01 h02 h12
    (by rw [hg]; linarith) (by rw [hg]; linarith) (by rw [hg]; linarith)
  have hs : g ⁻¹' {0} = f ⁻¹' {t} := by
    ext z
    change g z = 0 ↔ f z = t
    rw [hg, sub_eq_zero]
  rw [hs] at h
  simpa only [hg, affineLevelEdgePoint, levelEdgeParameter_shift] using h

theorem affine_triangle_level_slice_low (f : ℂ →ᵃ[ℝ] ℝ) (p₀ p₁ p₂ : ℂ)
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) {t : ℝ}
    (h0 : f p₀ < t) (h1 : t < f p₁) (h2 : t < f p₂) :
    convexHull ℝ ({p₀, p₁, p₂} : Set ℂ) ∩ f ⁻¹' {t} =
      segment ℝ (affineLevelEdgePoint p₀ p₁ (f p₀) (f p₁) t)
        (affineLevelEdgePoint p₀ p₂ (f p₀) (f p₂) t) := by
  have h := affine_triangle_level_slice_high (-f) p₀ p₁ p₂ h01 h02 h12 (t := -t)
    (by change -t < -f p₀; linarith) (by change -f p₁ < -t; linarith)
    (by change -f p₂ < -t; linarith)
  have hs : (-f) ⁻¹' {-t} = f ⁻¹' {t} := by
    ext z
    change -f z = -t ↔ f z = t
    exact neg_inj
  rw [hs] at h
  simpa only [AffineMap.coe_neg, Pi.neg_apply, affineLevelEdgePoint, levelEdgeParameter_neg] using h

theorem affine_triangle_slice_two_incident_edges (f : ℂ →ᵃ[ℝ] ℝ) (p₀ p₁ p₂ : ℂ)
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) {t : ℝ}
    (h1 : (f p₀ < t ∧ t < f p₁) ∨ (f p₁ < t ∧ t < f p₀))
    (h2 : (f p₀ < t ∧ t < f p₂) ∨ (f p₂ < t ∧ t < f p₀)) :
    convexHull ℝ ({p₀, p₁, p₂} : Set ℂ) ∩ f ⁻¹' {t} =
      segment ℝ (affineLevelEdgePoint p₀ p₁ (f p₀) (f p₁) t)
        (affineLevelEdgePoint p₀ p₂ (f p₀) (f p₂) t) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact affine_triangle_level_slice_low f p₀ p₁ p₂ h01 h02 h12 h1.1 h1.2 h2.2
  · linarith [h1.1, h2.2]
  · linarith [h1.2, h2.1]
  · exact affine_triangle_level_slice_high f p₀ p₁ p₂ h01 h02 h12 h1.2 h1.1 h2.1

end RepulsiveCoulomb
