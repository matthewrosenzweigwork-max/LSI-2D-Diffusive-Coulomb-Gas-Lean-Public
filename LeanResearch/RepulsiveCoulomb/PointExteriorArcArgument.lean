module

public import LeanResearch.RepulsiveCoulomb.PointExteriorConnectionEstimates
public import LeanResearch.RepulsiveCoulomb.PointArcObserverCorrection
public import LeanResearch.RepulsiveCoulomb.PointFiniteOpenArgument

@[expose] public section

/-! Exact weighted point-argument increments along an actual exterior arc.
The canonical correction is constructed from the literal finite product;
uniqueness of continuous lifts removes arbitrary branch choices. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem pointExterior_chord_ratio_re_pos {p z : ℂ} (hz : 0 < ‖z‖)
    (hp : 2 * ‖p‖ ≤ ‖z‖) : 0 < ((z - p) / (z - 0)).re := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  have hratio : (z - p) / (z - 0) = 1 - p / z := by
    simp only [sub_zero]
    rw [sub_div, div_self hz0]
  have hnorm := pointExterior_norm_div_le_half hz hp
  have hre := Complex.re_le_norm (p / z)
  rw [hratio, Complex.sub_re, Complex.one_re]
  linarith

/-- Actual open-edge puncture argument lifts have the exact exterior
increment, including the complete polar winding and the literal endpoint
phase correction. Zero-weight points need no lift identity. -/
theorem pointExterior_arc_weighted_argument_increment
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ)
    (hz : ∀ t, 0 < ‖γ t‖) (hy : ∀ j t, 2 * ‖y j‖ ≤ ‖γ t‖)
    (φ : Icc (0 : ℝ) 1 → ℝ) (hφ : Continuous φ)
    (hφl : ∀ t, Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ))
    (ψ : Fin m → Icc (0 : ℝ) 1 → ℝ) (hψ : ∀ j, Continuous (ψ j))
    (hψl : ∀ j, a j ≠ 0 → ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j t : ℂ) * Complex.I) = (γ t - y j) / (‖γ t - y j‖ : ℂ)) :
    (∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) =
      pointExteriorHalfMass a * (φ 1 - φ 0) +
        pointExteriorPhaseCorrection a y (γ 1) - pointExteriorPhaseCorrection a y (γ 0) := by
  have hterm (j : Fin m) : (a j / 2) * (ψ j 1 - ψ j 0) =
      (a j / 2) * (φ 1 - φ 0) +
        (a j / 2) * Complex.arg (1 - y j / γ 1) -
        (a j / 2) * Complex.arg (1 - y j / γ 0) := by
    by_cases haj : a j = 0
    · simp [haj]
    have hp : ∀ t, γ t ≠ y j := fun t => sub_ne_zero.mp (pointExterior_sub_ne_zero (hz t) (hy j t))
    have hclosed := point_argument_open_identity_extends_to_endpoints γ hγ (y j) hp
      (ψ j) (hψ j) (hψl j haj)
    have hcanonical := pointArcObserverArgument_continuous_lift hγ hφ
      (fun t => norm_pos_iff.mp (hz t)) hp
      (fun t => pointExterior_chord_ratio_re_pos (hz t) (hy j t))
      (by intro t; simpa only [sub_zero] using hφl t)
    have hinc := euclidean_angle_lift_increment_eq (hψ j) hcanonical.1
      (fun t => Circle.ext ((hclosed t).trans (hcanonical.2 t).symm))
      (0 : Icc (0 : ℝ) 1) 1
    have hratio (t : Icc (0 : ℝ) 1) : (γ t - y j) / (γ t - 0) = 1 - y j / γ t := by
      simp only [sub_zero]
      rw [sub_div, div_self (norm_pos_iff.mp (hz t))]
    simp only [pointArcObserverArgument, hratio] at hinc
    rw [hinc]
    ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hterm j)
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [pointExteriorPhaseCorrection_eq_arg_sum, pointExteriorPhaseCorrection_eq_arg_sum]
  unfold pointExteriorHalfMass
  rw [Finset.sum_mul]

/-- The full exterior endpoint correction on one large circle is bounded
by 2D/R, with D the already defined actual first-moment constant. -/
theorem pointExterior_circle_phase_correction_bound
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {R : ℝ} (hR : 0 < R) {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = R) (hz₁ : ‖z₁‖ = R)
    (hy : ∀ j, 2 * ‖y j‖ ≤ R) :
    |pointExteriorPhaseCorrection a y z₁ - pointExteriorPhaseCorrection a y z₀| ≤
      2 * pointExteriorMoment a y / R := by
  have h₀ := abs_pointExteriorPhaseCorrection_le ha y
    (show 0 < ‖z₀‖ by rw [hz₀]; exact hR) (fun j => by rw [hz₀]; exact hy j)
  have h₁ := abs_pointExteriorPhaseCorrection_le ha y
    (show 0 < ‖z₁‖ by rw [hz₁]; exact hR) (fun j => by rw [hz₁]; exact hy j)
  rw [hz₀] at h₀
  rw [hz₁] at h₁
  calc
    |pointExteriorPhaseCorrection a y z₁ - pointExteriorPhaseCorrection a y z₀| ≤
        |pointExteriorPhaseCorrection a y z₁| + |pointExteriorPhaseCorrection a y z₀| := abs_sub _ _
    _ ≤ pointExteriorMoment a y / R + pointExteriorMoment a y / R := add_le_add h₁ h₀
    _ = 2 * pointExteriorMoment a y / R := by ring

end RepulsiveCoulomb
