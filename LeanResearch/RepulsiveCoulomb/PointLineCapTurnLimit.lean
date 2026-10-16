import LeanResearch.RepulsiveCoulomb.PointLineCapAngleLimits
import LeanResearch.RepulsiveCoulomb.PointLineCapAtomSupport
import LeanResearch.RepulsiveCoulomb.PointCircleCapCovariantTurn
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Records-only, uncompiled. The literal circle covariant turn and literal
line/circle corner turns have the desired limit. This is not a signed side
mass theorem: applying mixed Gauss--Bonnet and identifying each on-line full
physical interval with its fixed side remain separate obligations. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RepulsiveCoulomb

/-- Exact circle contribution, whose equality to arbitrary actual lift
increments is proved below. The finite-product endpoint phase is retained. -/
def pointLineCapCircleTurn {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R : ℝ} (D : LineCapGeometry c R) : ℝ :=
  (1 + pointExteriorHalfMass a) * (D.beta - D.alpha) +
    pointExteriorPhaseCorrection a y (c D.minus) -
    pointExteriorPhaseCorrection a y (c D.plus)

theorem pointLineCapCircleTurn_eq_covariant_increment
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R : ℝ} (D : LineCapGeometry c R)
    (hy : ∀ j, 2 * ‖y j‖ ≤ R)
    (τ : Icc (0 : ℝ) 1 → ℝ) (hτ : Continuous τ)
    (hτl : ∀ t, Complex.exp ((τ t : ℂ) * Complex.I) =
      deriv (pointCircleCapArc R D.alpha D.beta) t /
        (‖deriv (pointCircleCapArc R D.alpha D.beta) t‖ : ℂ))
    (ψ : Fin m → Icc (0 : ℝ) 1 → ℝ) (hψ : ∀ j, Continuous (ψ j))
    (hψl : ∀ j, a j ≠ 0 → ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j t : ℂ) * Complex.I) =
        (pointCircleCapArc R D.alpha D.beta t - y j) /
          (‖pointCircleCapArc R D.alpha D.beta t - y j‖ : ℂ)) :
    pointLineCapCircleTurn a y D =
      (τ 1 - τ 0) + ∑ j, (a j / 2) * (ψ j 1 - ψ j 0) := by
  symm
  simpa only [pointLineCapCircleTurn, D.circle_zero, D.circle_one] using
    pointCircleCapArc_covariant_turn a y D.radius_pos D.angle_lt hy τ hτ hτl ψ hψ hψl

/-- This is an actual geometric expression, not a side-mass certificate. -/
def pointLineCapTurnDefect {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R : ℝ} (D : LineCapGeometry c R) : ℝ :=
  pointLineCapCircleTurn a y D +
    Complex.arg (deriv (pointCircleCapArc R D.alpha D.beta) 0 / deriv c D.plus) +
    Complex.arg (deriv c D.minus / deriv (pointCircleCapArc R D.alpha D.beta) 1) -
    2 * Real.pi

theorem lineCapFamilyAt_phase_correction_tendsto_zero
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R₀ : ℝ} (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) :
    Tendsto (fun r =>
      pointExteriorPhaseCorrection a y (c (lineCapFamilyAt C r).minus) -
      pointExteriorPhaseCorrection a y (c (lineCapFamilyAt C r).plus)) atTop (𝓝 0) := by
  obtain ⟨A, hA, hAy⟩ := lineCap_all_atoms_below_radius y
  have hbound : ∀ᶠ r in atTop,
      ‖pointExteriorPhaseCorrection a y (c (lineCapFamilyAt C r).minus) -
        pointExteriorPhaseCorrection a y (c (lineCapFamilyAt C r).plus)‖ ≤
          2 * pointExteriorMoment a y / lineCapLargeRadius R₀ r := by
    filter_upwards [(lineCapLargeRadius_tendsto R₀).eventually_ge_atTop (2 * A)] with r hr
    let D := lineCapFamilyAt C r
    have hy : ∀ j, 2 * ‖y j‖ ≤ lineCapLargeRadius R₀ r := by
      intro j
      have hj := hAy A le_rfl j
      linarith
    simpa only [Real.norm_eq_abs] using pointExterior_circle_phase_correction_bound ha y
      D.radius_pos ((D.crosses D.plus).mpr (Or.inr rfl))
      ((D.crosses D.minus).mpr (Or.inl rfl)) hy
  have hzero : Tendsto (fun r => 2 * pointExteriorMoment a y / lineCapLargeRadius R₀ r)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (lineCapLargeRadius_tendsto R₀)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hzero

theorem lineCapFamilyAt_circle_turn_tendsto
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R₀ : ℝ} (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hp : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hm : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ))) :
    Tendsto (fun r => pointLineCapCircleTurn a y (lineCapFamilyAt C r))
      atTop (𝓝 ((1 + pointExteriorHalfMass a) * Real.pi)) := by
  have h := ((lineCapFamilyAt_width_tendsto C hp hm).const_mul (1 + pointExteriorHalfMass a)).add
    (lineCapFamilyAt_phase_correction_tendsto_zero ha y C)
  simpa only [pointLineCapCircleTurn, add_sub_assoc, add_zero] using h

theorem lineCapFamilyAt_turn_defect_tendsto
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R₀ : ℝ} (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hp : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hm : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)))
    (hvp : Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) -
      c t / (‖c t‖ : ℂ)) atTop (𝓝 0))
    (hvm : Tendsto (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) -
      c t / (‖c t‖ : ℂ)) atBot (𝓝 0)) :
    Tendsto (fun r => pointLineCapTurnDefect a y (lineCapFamilyAt C r))
      atTop (𝓝 (Real.pi * pointExteriorHalfMass a)) := by
  obtain ⟨hcp, hcm⟩ := lineCapFamilyAt_corner_turn_limits C hp hm hvp hvm
  have h := (((lineCapFamilyAt_circle_turn_tendsto ha y C hp hm).add hcp).add hcm).sub_const
    (2 * Real.pi)
  have he : (1 + pointExteriorHalfMass a) * Real.pi + Real.pi / 2 +
      Real.pi / 2 - 2 * Real.pi = Real.pi * pointExteriorHalfMass a := by ring
  simpa only [pointLineCapTurnDefect, he] using h

/-- The actual-tail constructor supplies every analytic hypothesis. This
endpoint is from the original finite nonnegative inputs and positive B. Its
conclusion is deliberately the actual cap turn limit, not a claimed balance. -/
theorem exists_pointConformal_actual_cap_with_turn_limit
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      ∃ R₀ s : ℝ, 0 < R₀ ∧ ‖c s‖ < R₀ ∧ DifferentiableAt ℝ c s ∧ deriv c s ≠ 0 ∧
        ∃ C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R,
          Tendsto (fun r => pointLineCapTurnDefect a y (lineCapFamilyAt C r))
            atTop (𝓝 (Real.pi * pointExteriorHalfMass a)) := by
  obtain ⟨c, hc, hd, hp, hm, T, hT, htp, htm, hvp, hvm⟩ :=
    exists_pointConformal_complete_line_with_actual_radial_tails ha y hB
  obtain ⟨R₀, s, hR₀, hsR, hds, hvs, ⟨C⟩⟩ :=
    exists_pointMetricLine_actual_cap_family ha y c hd hT htp htm
  exact ⟨c, hc, hd, R₀, s, hR₀, hsR, hds, hvs, C,
    lineCapFamilyAt_turn_defect_tendsto ha y C hp hm hvp hvm⟩

end RepulsiveCoulomb
