module

public import LeanResearch.RepulsiveCoulomb.HolomorphicRadialArc
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

@[expose] public section

/-! A real-analytic arc near the closed unit interval has a global smooth
extension agreeing on a neighborhood of every point of that interval. In
particular its actual endpoint derivatives are preserved. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem analytic_unitInterval_global_smooth_extension (f : ℝ → ℂ)
    (hf : AnalyticOnNhd ℝ f (Icc (0 : ℝ) 1)) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
      ∀ x ∈ Icc (0 : ℝ) 1, g =ᶠ[𝓝 x] f := by
  have hI : closedBall (1 / 2 : ℝ) (1 / 2) = Icc (0 : ℝ) 1 := by
    rw [Real.closedBall_eq_Icc]
    norm_num
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (1 / 2 : ℝ) (1 / 2)).exists_cthickening_subset_open
    (isOpen_analyticAt ℝ f) (by intro x hx; exact hf x (hI ▸ hx))
  rw [cthickening_closedBall hδ.le (by norm_num)] at hsub
  let χ : ContDiffBump (1 / 2 : ℝ) :=
    ⟨1 / 2 + δ / 2, δ + 1 / 2, by positivity, by linarith⟩
  let g : ℝ → ℂ := fun t => χ t • f t
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (χ : ℝ → ℝ)
    · have ha : AnalyticAt ℝ f x := hsub (by simpa only [χ.tsupport_eq] using hx)
      exact χ.contDiff.contDiffAt.smul ha.contDiffAt
    · have hz : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with t ht
        simp only [g, ht, zero_smul, Pi.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  refine ⟨g, hG, ?_⟩
  intro x hx
  have hdist : dist x (1 / 2 : ℝ) ≤ 1 / 2 := by
    apply mem_closedBall.mp
    rwa [hI]
  have hmem : x ∈ ball (1 / 2 : ℝ) χ.rIn := by
    change dist x (1 / 2 : ℝ) < 1 / 2 + δ / 2
    linarith
  filter_upwards [isOpen_ball.mem_nhds hmem] with t ht
  change χ t • f t = f t
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall ht), one_smul]

end RepulsiveCoulomb
