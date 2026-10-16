import LeanResearch.RepulsiveCoulomb.PointCoreLocalSPI

/-! Actual L1 and L2 mass controls for the inner/outer smooth-core split. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointCore_cutoff_mass_split {m : ℕ} {γ R : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hR : 0 < R)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
      2 * (∫ x, (pointCoreInnerCutoff R hR φ x) ^ 2 ∂pointMeasure γ a y) +
      2 * (∫ x, (pointCoreOuterCutoff R hR φ x) ^ 2 ∂pointMeasure γ a y) := by
  let _ := pointMeasure_isProbability hγ ha y
  have hi (ψ : TestFunction (pointDomain a y) ℝ ⊤) :
      Integrable (fun x : ℂ => ψ x ^ 2) (pointMeasure γ a y) := by
    have hs : HasCompactSupport (fun x : ℂ => ψ x ^ 2) :=
      ψ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact (ψ.continuous.pow 2).integrable_of_hasCompactSupport hs
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi (pointCoreInnerCutoff R hR φ)).const_mul 2)
      ((hi (pointCoreOuterCutoff R hR φ)).const_mul 2)]
  apply integral_mono (hi φ) (((hi (pointCoreInnerCutoff R hR φ)).const_mul 2).add
    ((hi (pointCoreOuterCutoff R hR φ)).const_mul 2))
  intro x
  change φ x ^ 2 ≤ 2 * (pointCoreInnerCutoff R hR φ x) ^ 2 + 2 * (pointCoreOuterCutoff R hR φ x) ^ 2
  have he := pointCore_cutoff_decomposition R hR φ x
  rw [← he]
  nlinarith [sq_nonneg (pointCoreInnerCutoff R hR φ x - pointCoreOuterCutoff R hR φ x)]

theorem pointCore_inner_cutoff_l1 {m : ℕ} {γ R : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hR : 0 < R)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, |pointCoreInnerCutoff R hR φ x| ∂pointMeasure γ a y) ≤
      ∫ x, |φ x| ∂pointMeasure γ a y := by
  let _ := pointMeasure_isProbability hγ ha y
  have hi (ψ : TestFunction (pointDomain a y) ℝ ⊤) :
      Integrable (fun x : ℂ => |ψ x|) (pointMeasure γ a y) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).abs
  exact integral_mono (hi _) (hi φ) (pointCore_inner_cutoff_abs_le R hR φ)

end RepulsiveCoulomb
