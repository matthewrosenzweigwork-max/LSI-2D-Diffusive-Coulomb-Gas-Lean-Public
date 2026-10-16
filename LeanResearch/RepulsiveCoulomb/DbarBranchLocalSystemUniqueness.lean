import LeanResearch.RepulsiveCoulomb.DbarBranchLocalSystemRepresentatives
import LeanResearch.RepulsiveCoulomb.DbarBranchLocalDistribution

/-! The actual injective distributional representation identifies two
weighted-L2 outputs of the same local weak system. This is operator-output
uniqueness, with no weak regularity or graph-density assumption. -/
noncomputable section
open Set MeasureTheory
open scoped Distributions
namespace RepulsiveCoulomb

theorem dbarLocalWeakSystem_output_unique_L2 {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    {A : κ → ι → δ → CoulombConfig N → ℂ} {B : κ → ι → CoulombConfig N → ℂ}
    {v : δ → CoulombConfig N} {u : ι → CoulombConfig N → ℂ}
    {g g' : κ → Lp ℂ 2 (coulombMeasure N β)}
    (hg : DbarLocalWeakSystem A B v u (fun a => (g a : CoulombConfig N → ℂ)))
    (hg' : DbarLocalWeakSystem A B v u (fun a => (g' a : CoulombConfig N → ℂ))) : g = g' := by
  funext a
  apply coulombL2Distribution_injective hβ
  apply ContinuousLinearMap.ext
  intro φ
  exact (coulombL2Distribution_apply hβ (g a) φ).trans
    ((hg a φ).trans ((hg' a φ).symm.trans
      (coulombL2Distribution_apply hβ (g' a) φ).symm))

end RepulsiveCoulomb
