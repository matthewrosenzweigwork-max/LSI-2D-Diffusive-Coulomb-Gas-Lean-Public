import LeanResearch.RepulsiveCoulomb.AffineLevelEdge

/-! Explicit redistribution of barycentric weights on a triangle cut by a line.
The slice is a segment between the two genuine edge crossings. -/
noncomputable section
open Set AffineMap
namespace RepulsiveCoulomb

theorem barycentric_zero_mem_crossing_segment (p₀ p₁ p₂ : ℂ)
    {a₀ a₁ a₂ l₀ l₁ l₂ : ℝ} (ha₀ : 0 < a₀) (ha₁ : a₁ < 0) (ha₂ : a₂ < 0)
    (hl₀ : 0 ≤ l₀) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hls : l₀ + l₁ + l₂ = 1) (hlz : l₀ * a₀ + l₁ * a₁ + l₂ * a₂ = 0) :
    l₀ • p₀ + l₁ • p₁ + l₂ • p₂ ∈
      segment ℝ (affineLevelEdgePoint p₀ p₁ a₀ a₁ 0)
        (affineLevelEdgePoint p₀ p₂ a₀ a₂ 0) := by
  let r := l₁ * (a₀ - a₁) / a₀
  let s := l₂ * (a₀ - a₂) / a₀
  have hd₁ : a₀ - a₁ ≠ 0 := by linarith
  have hd₂ : a₀ - a₂ ≠ 0 := by linarith
  have he₁ : a₁ - a₀ ≠ 0 := by linarith
  have he₂ : a₂ - a₀ ≠ 0 := by linarith
  have hr : 0 ≤ r := div_nonneg (mul_nonneg hl₁ (by linarith)) ha₀.le
  have hs : 0 ≤ s := div_nonneg (mul_nonneg hl₂ (by linarith)) ha₀.le
  have hrs : r + s = 1 := by
    dsimp [r, s]
    rw [← add_div, div_eq_one_iff_eq ha₀.ne']
    have hh : a₀ * (l₀ + l₁ + l₂) = a₀ := by rw [hls, mul_one]
    nlinarith
  have h₁ : r * levelEdgeParameter a₀ a₁ 0 = l₁ := by
    dsimp [r, levelEdgeParameter]
    field_simp [ha₀.ne', he₁]
    <;> ring
  have h₂ : s * levelEdgeParameter a₀ a₂ 0 = l₂ := by
    dsimp [s, levelEdgeParameter]
    field_simp [ha₀.ne', he₂]
    <;> ring
  have h₀ : r * (1 - levelEdgeParameter a₀ a₁ 0) +
      s * (1 - levelEdgeParameter a₀ a₂ 0) = l₀ := by
    nlinarith [h₁, h₂]
  refine ⟨r, s, hr, hs, hrs, ?_⟩
  unfold affineLevelEdgePoint
  rw [lineMap_apply_module, lineMap_apply_module]
  calc
    _ = (r * (1 - levelEdgeParameter a₀ a₁ 0) + s * (1 - levelEdgeParameter a₀ a₂ 0)) • p₀ +
        (r * levelEdgeParameter a₀ a₁ 0) • p₁ + (s * levelEdgeParameter a₀ a₂ 0) • p₂ := by module
    _ = _ := by rw [h₀, h₁, h₂]

end RepulsiveCoulomb
