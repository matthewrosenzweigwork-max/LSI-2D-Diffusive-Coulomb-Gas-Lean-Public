module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Literal contour points on an affine edge, determined only by endpoint values.
This makes shared-edge consistency independent of the adjacent triangle formula. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

def levelEdgeParameter (u v t : ℝ) : ℝ := (t - u) / (v - u)

def affineLevelEdgePoint (p q : ℂ) (u v t : ℝ) : ℂ :=
  lineMap p q (levelEdgeParameter u v t)

theorem levelEdgeParameter_value {u v : ℝ} (huv : u ≠ v) (t : ℝ) :
    u + (v - u) * levelEdgeParameter u v t = t := by
  unfold levelEdgeParameter
  field_simp [sub_ne_zero.mpr huv.symm]
  <;> ring

theorem levelEdgeParameter_reverse {u v : ℝ} (huv : u ≠ v) (t : ℝ) :
    levelEdgeParameter v u t = 1 - levelEdgeParameter u v t := by
  unfold levelEdgeParameter
  field_simp [sub_ne_zero.mpr huv, sub_ne_zero.mpr huv.symm]
  <;> ring

theorem levelEdgeParameter_mem_Ioo {u v t : ℝ}
    (h : (u < t ∧ t < v) ∨ (v < t ∧ t < u)) : levelEdgeParameter u v t ∈ Ioo 0 1 := by
  unfold levelEdgeParameter
  rcases h with h | h
  · have hd : 0 < v - u := by linarith
    exact ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩
  · have hd : v - u < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg (by linarith) hd,
      (div_lt_one_of_neg hd).mpr (by linarith)⟩

theorem affineLevelEdgePoint_reverse (p q : ℂ) {u v : ℝ} (huv : u ≠ v) (t : ℝ) :
    affineLevelEdgePoint q p v u t = affineLevelEdgePoint p q u v t := by
  unfold affineLevelEdgePoint
  rw [levelEdgeParameter_reverse huv t, lineMap_apply_one_sub]

theorem affineLevelEdgePoint_mem_openSegment (p q : ℂ) {u v t : ℝ}
    (h : (u < t ∧ t < v) ∨ (v < t ∧ t < u)) :
    affineLevelEdgePoint p q u v t ∈ openSegment ℝ p q := by
  rw [openSegment_eq_image_lineMap]
  exact ⟨levelEdgeParameter u v t, levelEdgeParameter_mem_Ioo h, rfl⟩

theorem affineLevelEdgePoint_apply (f : ℂ →ᵃ[ℝ] ℝ) (p q : ℂ)
    (h : f p ≠ f q) (t : ℝ) :
    f (affineLevelEdgePoint p q (f p) (f q) t) = t := by
  unfold affineLevelEdgePoint
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
  simp only [smul_eq_mul]
  have hh := levelEdgeParameter_value h t
  nlinarith

theorem affineLevelEdgePoint_unique (f : ℂ →ᵃ[ℝ] ℝ) (p q : ℂ)
    (h : f p ≠ f q) {t : ℝ} {x : ℂ} (hx : x ∈ segment ℝ p q) (hfx : f x = t) :
    x = affineLevelEdgePoint p q (f p) (f q) t := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r, _, rfl⟩ := hx
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module] at hfx
  simp only [smul_eq_mul] at hfx
  have hv := levelEdgeParameter_value h t
  have hr : r = levelEdgeParameter (f p) (f q) t := by
    have hn : f q - f p ≠ 0 := sub_ne_zero.mpr h.symm
    apply (mul_right_cancel₀ hn)
    nlinarith
  rw [hr]
  rfl

end RepulsiveCoulomb
