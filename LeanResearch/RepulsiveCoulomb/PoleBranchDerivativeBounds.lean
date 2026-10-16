import Mathlib.Analysis.Complex.Schwarz

/-! Local Frechet-derivative bounds for the genuine holomorphic class in arbitrary
complex normed spaces. No several-variable analyticity assumption is introduced. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

 theorem poleBranch_fderiv_norm_le_inner_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {c y : E} {R r M : ℝ}
    (hrR : r < R) (hy : y ∈ ball c r)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ x ∈ ball c R, ‖f x‖ ≤ M) :
    ‖fderiv ℂ f y‖ ≤ (2 * M) / (R - r) := by
  have hsub : ball y (R - r) ⊆ ball c R := by
    intro x hx
    have hx' := mem_ball.mp hx
    have hy' := mem_ball.mp hy
    apply mem_ball.mpr
    calc
      dist x c ≤ dist x y + dist y c := dist_triangle _ _ _
      _ < R := by linarith
  have hyR : y ∈ ball c R := ball_subset_ball hrR.le hy
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) ?_ (sub_pos.mpr hrR)
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hb x (hsub hx)) (hb y hyR)
    _ = 2 * M := by ring

end RepulsiveCoulomb
