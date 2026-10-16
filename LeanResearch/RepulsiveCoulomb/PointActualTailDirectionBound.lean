import LeanResearch.RepulsiveCoulomb.PointActualTailEndpointBound
import LeanResearch.RepulsiveCoulomb.DirectionalTailLimits
import Mathlib.Tactic

/-! Uncompiled additive successor. Actual last-circle-crossing direction bound
for an original finite-segment endpoint, with all angle lifts eliminated from
the final estimate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_actual_tail_endpoint_direction_bound
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {A k : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hk : k ∈ Icc (0 : ℝ) 1) (hanchor : ‖γ k‖ < A) (hend : A < ‖γ 1‖) :
    ∃ s ∈ Ioo k 1, ‖γ s‖ = A ∧ (∀ t ∈ Ioc s 1, A < ‖γ t‖) ∧
      ∀ t ∈ Ioo s 1,
        tailSineEnvelope A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖γ t‖ ≤ 1 / 2 →
        ‖γ t / (‖γ t‖ : ℂ) - γ 1 / (‖γ 1‖ : ℂ)‖ ≤
          angularTailPotential A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖γ t‖ := by
  obtain ⟨s, hs, hstart, hout, φ, hφ, hlift, hbound⟩ :=
    exists_pointConformal_actual_tail_endpoint_angle_bound ha y γ hc L hL hgeo
      hA hyA hB hD hk hanchor hend
  refine ⟨s, hs, hstart, hout, ?_⟩
  intro t ht hsmall
  have hangle := hbound t ht hsmall
  calc
    ‖γ t / (‖γ t‖ : ℂ) - γ 1 / (‖γ 1‖ : ℂ)‖ =
        ‖Complex.exp ((φ t : ℂ) * Complex.I) - Complex.exp ((φ 1 : ℂ) * Complex.I)‖ := by
      rw [hlift t ⟨ht.1.le, ht.2.le⟩, hlift 1 ⟨hs.2.le, le_rfl⟩]
    _ ≤ |φ t - φ 1| := norm_complex_angle_increment_le _ _
    _ ≤ angularTailPotential A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖γ t‖ := by
      simpa only [abs_sub_comm] using hangle

end RepulsiveCoulomb
