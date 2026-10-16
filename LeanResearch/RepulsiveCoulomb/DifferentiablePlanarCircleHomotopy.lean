module

public import LeanResearch.RepulsiveCoulomb.PlanarCircleLinearWinding
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

/-!
The actual first-order straight homotopy on sufficiently small circles.
A positive lower stretch makes the derivative term dominate the uniform
little-o remainder. Continuity of F is a separate topological hypothesis:
differentiability at the center alone does not make the entire circle image
continuous. Records-only candidate: not compiled or accepted.
-/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- The literal derivative-to-map homotopy; `s=0` is the actual image vector,
and `s=1` is its real-linear first-order approximation. -/
def planarDerivativeCircleHomotopy (F : ℂ → ℂ) (z : ℂ) (A : ℂ →L[ℝ] ℂ)
    (r : ℝ) (q : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : ℂ :=
  A (planarCircleVector r q.2) + (1 - (q.1 : ℝ)) •
    (F (z + planarCircleVector r q.2) - F z - A (planarCircleVector r q.2))

theorem planarDerivativeCircleHomotopy_continuous
    {F : ℂ → ℂ} (hF : Continuous F) (z : ℂ) (A : ℂ →L[ℝ] ℂ) (r : ℝ) :
    Continuous (planarDerivativeCircleHomotopy F z A r) := by
  have hc : Continuous (fun q : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
      planarCircleVector r q.2) :=
    (planarSignedCircleVector_continuous r 1).comp continuous_snd
  exact (A.continuous.comp hc).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (((hF.comp (continuous_const.add hc)).sub continuous_const).sub
        (A.continuous.comp hc)))

theorem planarDerivativeCircleHomotopy_zero (F : ℂ → ℂ) (z : ℂ)
    (A : ℂ →L[ℝ] ℂ) (r : ℝ) (t : Icc (0 : ℝ) 1) :
    planarDerivativeCircleHomotopy F z A r (0, t) = F (z + planarCircleVector r t) - F z := by
  simp [planarDerivativeCircleHomotopy]

theorem planarDerivativeCircleHomotopy_one (F : ℂ → ℂ) (z : ℂ)
    (A : ℂ →L[ℝ] ℂ) (r : ℝ) (t : Icc (0 : ℝ) 1) :
    planarDerivativeCircleHomotopy F z A r (1, t) = A (planarCircleVector r t) := by
  simp [planarDerivativeCircleHomotopy]

theorem planarDerivativeCircleHomotopy_closed (F : ℂ → ℂ) (z : ℂ)
    (A : ℂ →L[ℝ] ℂ) (r : ℝ) (s : Icc (0 : ℝ) 1) :
    planarDerivativeCircleHomotopy F z A r (s, 0) =
      planarDerivativeCircleHomotopy F z A r (s, 1) := by
  simp only [planarDerivativeCircleHomotopy, planarCircleVector_closed]

/-- Uniform first-order approximation gives one radius valid in every
circle direction and at every homotopy parameter. -/
theorem hasFDerivAt_small_circle_homotopy_avoids_zero
    {F : ℂ → ℂ} {z : ℂ} {A : ℂ →L[ℝ] ℂ} (hF : HasFDerivAt F A z)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) :
    ∃ R > 0, ∀ r, 0 < r → r < R →
      ∀ q, planarDerivativeCircleHomotopy F z A r q ≠ 0 := by
  have herr : ∀ᶠ h : ℂ in 𝓝 0,
      ‖F (z + h) - F z - A h‖ ≤ (c / 2) * ‖h‖ :=
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF).bound (half_pos hc)
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp herr
  refine ⟨R, hR, fun r hr hrR q => ?_⟩
  have hcircle : ‖planarCircleVector r q.2‖ = r :=
    planarSignedCircleVector_norm hr.le 1 q.2
  have he : ‖F (z + planarCircleVector r q.2) - F z - A (planarCircleVector r q.2)‖ ≤
      (c / 2) * ‖planarCircleVector r q.2‖ :=
    hball (show planarCircleVector r q.2 ∈ ball (0 : ℂ) R by
      simpa only [mem_ball, dist_zero_right, hcircle] using hrR)
  have hl := hlower (planarCircleVector r q.2)
  have hsmall : ‖F (z + planarCircleVector r q.2) - F z - A (planarCircleVector r q.2)‖ <
      ‖A (planarCircleVector r q.2)‖ := by
    rw [hcircle] at he hl
    nlinarith
  exact planar_add_small_smul_ne_zero hsmall q.1

/-- Continuous argument lifts of the actual small-circle image and the actual
derivative ellipse have equal increments, by the constructed avoiding square. -/
theorem hasFDerivAt_small_circle_argument_increment
    {F : ℂ → ℂ} (hcont : Continuous F) {z : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hF : HasFDerivAt F A z) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) :
    ∃ R > 0, ∀ r, 0 < r → r < R →
      ∀ (θ ψ : Icc (0 : ℝ) 1 → ℝ),
        PlanarArgumentLift (fun t => F (z + planarCircleVector r t) - F z) θ →
        PlanarArgumentLift (fun t => A (planarCircleVector r t)) ψ →
        θ 1 - θ 0 = ψ 1 - ψ 0 := by
  obtain ⟨R, hR, hav⟩ := hasFDerivAt_small_circle_homotopy_avoids_zero hF hc hlower
  refine ⟨R, hR, fun r hr hrR θ ψ hθ hψ => ?_⟩
  apply closed_vector_loop_argument_homotopy (planarDerivativeCircleHomotopy F z A r)
    (planarDerivativeCircleHomotopy_continuous hcont z A r) (hav r hr hrR)
    (planarDerivativeCircleHomotopy_closed F z A r) θ ψ hθ.1 hψ.1
  · simpa only [planarDerivativeCircleHomotopy_zero] using hθ.2
  · simpa only [planarDerivativeCircleHomotopy_one] using hψ.2

end RepulsiveCoulomb
