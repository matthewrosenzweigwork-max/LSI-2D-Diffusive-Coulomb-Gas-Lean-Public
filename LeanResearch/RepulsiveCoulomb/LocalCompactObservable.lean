import LeanResearch.RepulsiveCoulomb.PointCutoffBump

/-! An actual compactly supported C1 extension agreeing locally with any C1
observable throughout a prescribed closed ball. No constant enters coarea. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_compact_c1_agree_on_closedBall {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ g : ℂ → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      ∀ z ∈ closedBall c R, g =ᶠ[𝓝 z] f := by
  let b : ContDiffBump c := ⟨2 * R, 3 * R, by positivity, by linarith⟩
  let g : ℂ → ℝ := fun z => b z * f z
  have hbC : ContDiff ℝ 1 b := b.contDiff
  refine ⟨g, hbC.mul hf, b.hasCompactSupport.mul_right, ?_⟩
  intro z hz
  have hb : z ∈ ball c b.rIn := by
    change dist z c < 2 * R
    have hh : dist z c ≤ R := hz
    linarith
  filter_upwards [b.eventuallyEq_one_of_mem_ball hb] with x hx
  change b x * f x = f x
  rw [show b x = 1 from hx, one_mul]

theorem gradient_eq_of_eventuallyEq {f g : ℂ → ℝ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : gradient f z = gradient g z := by
  unfold gradient
  rw [h.fderiv_eq]

end RepulsiveCoulomb
