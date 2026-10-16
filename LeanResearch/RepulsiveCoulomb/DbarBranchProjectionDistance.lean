import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCurvatureDuality
import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelRegularity

/-! Recover the original Euclidean weak graph from the curvature-weighted
auxiliary solution, then use the actual original projection's minimality.
The estimate has its literal 2/beta coefficient on the full original weak
graph; no auxiliary-kernel identification or extra regularity is assumed. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

theorem coulombDbarWeakGraph_small_solution {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombMaxDbarGraph hβ) :
    ∃ s : Lp ℂ 2 (coulombMeasure N β), (s, g) ∈ coulombMaxDbarGraph hβ ∧
      ‖s‖ ^ 2 ≤ (2 / β) * ‖g‖ ^ 2 := by
  obtain ⟨s, hs, hnorm⟩ := coulombAuxiliary_curvature_solution hβ g
    (coulombAuxiliary_original_datum_mem_compatibility hβ hfg)
  exact ⟨s, coulombAuxiliaryMinimalGraph_original_datum hβ hs, hnorm⟩

theorem coulombDbarWeakProjection_distance_sq_le {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombMaxDbarGraph hβ) :
    ‖f - coulombDbarWeakProjection N hβ f‖ ^ 2 ≤ (2 / β) * ‖g‖ ^ 2 := by
  obtain ⟨s, hs, hnorm⟩ := coulombDbarWeakGraph_small_solution hβ hfg
  have hmin := coulombDbarWeakProjection_residual_minimal hβ hfg hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hmin 2).trans hnorm

theorem coulombComplexCore_projection_distance_sq_le {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    ‖coulombComplexCoreValue hβ φ -
      coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ φ)‖ ^ 2 ≤
        (2 / β) * ‖coulombComplexCoreDbar hβ φ‖ ^ 2 :=
  coulombDbarWeakProjection_distance_sq_le hβ (coulombComplexCore_mem_maxDbarGraph hβ φ)

end RepulsiveCoulomb
