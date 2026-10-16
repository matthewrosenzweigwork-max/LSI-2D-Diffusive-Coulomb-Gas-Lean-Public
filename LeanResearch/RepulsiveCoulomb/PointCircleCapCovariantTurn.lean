import LeanResearch.RepulsiveCoulomb.PointExteriorArcArgument
import LeanResearch.RepulsiveCoulomb.PointCircleCapArc

/-! Exact covariant turning of a large positively oriented circle cap for
the literal finite-point conformal metric. The endpoint correction and its
2D/R bound are derived for arbitrary actual tangent/point lifts. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The full circle-cap covariant increment, including the endpoint phase
of the actual finite product, and without discarding angles beyond π. -/
theorem pointCircleCapArc_covariant_turn
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {R α β : ℝ} (hR : 0 < R) (hαβ : α < β) (hy : ∀ j, 2 * ‖y j‖ ≤ R)
    (τ : Icc (0 : ℝ) 1 → ℝ) (hτ : Continuous τ)
    (hτl : ∀ t, Complex.exp ((τ t : ℂ) * Complex.I) =
      deriv (pointCircleCapArc R α β) t / (‖deriv (pointCircleCapArc R α β) t‖ : ℂ))
    (ψ : Fin m → Icc (0 : ℝ) 1 → ℝ) (hψ : ∀ j, Continuous (ψ j))
    (hψl : ∀ j, a j ≠ 0 → ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j t : ℂ) * Complex.I) =
        (pointCircleCapArc R α β t - y j) / (‖pointCircleCapArc R α β t - y j‖ : ℂ)) :
    (τ 1 - τ 0) + (∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) =
      (1 + pointExteriorHalfMass a) * (β - α) +
        pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 1) -
        pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 0) := by
  have hturn := pointCircleCapArc_tangent_increment hR hαβ τ hτ hτl
  have hγ : Continuous (fun t : Icc (0 : ℝ) 1 => pointCircleCapArc R α β t) :=
    (pointCircleCapArc_smooth R α β).continuous.comp continuous_subtype_val
  have hflux := pointExterior_arc_weighted_argument_increment a y
    (fun t : Icc (0 : ℝ) 1 => pointCircleCapArc R α β t) hγ
    (fun t => by rw [pointCircleCapArc_norm hR.le]; exact hR)
    (fun j t => by rw [pointCircleCapArc_norm hR.le]; exact hy j)
    (fun t : Icc (0 : ℝ) 1 => α + (β - α) * t.1)
    (by fun_prop) (fun t => pointCircleCapArc_polar_lift hR α β t) ψ hψ hψl
  have hflux' : (∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) =
      pointExteriorHalfMass a * (β - α) +
        pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 1) -
        pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 0) := by
    simpa using hflux
  rw [hturn, hflux']
  ring

/-- The exact cap value differs from (1+B) times its full angular width by
at most 2D/R. This uses the actual first-moment and no abstract flux bound. -/
theorem pointCircleCapArc_covariant_turn_error
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {R α β : ℝ} (hR : 0 < R) (hαβ : α < β) (hy : ∀ j, 2 * ‖y j‖ ≤ R)
    (τ : Icc (0 : ℝ) 1 → ℝ) (hτ : Continuous τ)
    (hτl : ∀ t, Complex.exp ((τ t : ℂ) * Complex.I) =
      deriv (pointCircleCapArc R α β) t / (‖deriv (pointCircleCapArc R α β) t‖ : ℂ))
    (ψ : Fin m → Icc (0 : ℝ) 1 → ℝ) (hψ : ∀ j, Continuous (ψ j))
    (hψl : ∀ j, a j ≠ 0 → ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j t : ℂ) * Complex.I) =
        (pointCircleCapArc R α β t - y j) / (‖pointCircleCapArc R α β t - y j‖ : ℂ)) :
    |((τ 1 - τ 0) + (∑ j, (a j / 2) * (ψ j 1 - ψ j 0))) -
      (1 + pointExteriorHalfMass a) * (β - α)| ≤ 2 * pointExteriorMoment a y / R := by
  rw [pointCircleCapArc_covariant_turn a y hR hαβ hy τ hτ hτl ψ hψ hψl]
  have heq : (1 + pointExteriorHalfMass a) * (β - α) +
      pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 1) -
      pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 0) -
      (1 + pointExteriorHalfMass a) * (β - α) =
      pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 1) -
      pointExteriorPhaseCorrection a y (pointCircleCapArc R α β 0) := by ring
  rw [heq]
  exact pointExterior_circle_phase_correction_bound ha y hR
    (pointCircleCapArc_norm hR.le α β 0) (pointCircleCapArc_norm hR.le α β 1) hy

end RepulsiveCoulomb
