module

public import LeanResearch.RepulsiveCoulomb.PointChosenSmoothRadialChart
public import LeanResearch.RepulsiveCoulomb.PointClassicalConeChart
public import LeanResearch.RepulsiveCoulomb.PointGeodesicOrientedClock
public import LeanResearch.RepulsiveCoulomb.PointLineFullIntervalWidth
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Uncompiled records-only successor. Recover the metric information retained
by the construction of the chosen smooth chart, then use THAT SAME chart to
construct a classical-cone local isometry. The transition is an explicit
positive radial power: full polar angles and side order are not inferred from
chord distances or principal arguments. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- The stronger underlying constructor retained this exact power-cone
identity. Recover it without modifying the accepted chosen-chart API. -/
theorem pointChosenSmoothRadialChart_power_metric_spec
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    let e := pointChosenSmoothRadialChart ha y p
    ∃ R : ℝ, 0 < R ∧ e p = 0 ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ∈ e.source) ∧
      ∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          pointSmoothConformalEDist a y u v =
            pointSmoothConformalEDist (standardConeExponents (coalescedPointExponent a y p / 2))
              standardConeLocations (e u) (e v) := by
  obtain ⟨R, hR, hep, _, _, hsource, hmetric, _⟩ :=
    Classical.choose_spec (exists_pointConformal_smooth_radial_germ_chart ha y p)
  exact ⟨R, hR, hep, hsource, hmetric⟩

/-- Full complex-coordinate identity for a positive radius. It records the
unmodified real angle phi, so reflex intervals survive the transition. -/
theorem coneRadialEquiv_polar_exact {α r : ℝ} (hα : 0 ≤ α) (hr : 0 < r) (φ : ℝ) :
    coneRadialEquiv α hα (pointRadialSectorPoint r φ) =
      pointRadialSectorPoint (r ^ (α + 1) / (α + 1)) φ := by
  change (α + 1)⁻¹ • (‖pointRadialSectorPoint r φ‖ ^ (α + 1 - 1) •
    pointRadialSectorPoint r φ) = _
  rw [pointRadialSectorPoint_norm hr.le]
  simp only [add_sub_cancel_right, smul_smul, pointRadialSectorPoint, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div]
  have hpow : r ^ α * r = r ^ (α + 1) := (Real.rpow_add_one hr.ne' α).symm
  have hpowC := congrArg (fun t : ℝ => (t : ℂ)) hpow
  push_cast at hpowC
  calc
    _ = (((α + 1 : ℝ) : ℂ)⁻¹ * (((r ^ α : ℝ) : ℂ) * r)) *
      (Circle.exp φ : ℂ) := by ring
    _ = (((r ^ (α + 1) : ℝ) : ℂ) / ((α + 1 : ℝ) : ℂ)) * (Circle.exp φ : ℂ) := by
      rw [hpowC]
      ring

/-- Positive real scaling preserves the full normalized direction, including
across the principal-argument cut. -/
theorem coneRadialEquiv_normalized_exact {α : ℝ} (hα : 0 ≤ α) (z : ℂ) :
    coneRadialEquiv α hα z / (‖coneRadialEquiv α hα z‖ : ℂ) = z / (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, coneRadialEquiv_zero]
  · simp only [coneRadialEquiv, complexRadialPower, add_sub_cancel_right, smul_smul]
    exact normalized_complex_smul_pos hz
      (mul_pos (inv_pos.mpr (by linarith)) (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) α))

/-- A classical-cone chart constructed from the literal same chosen smooth
chart. It is only radially reparameterized, with no angular conjugation or
reflection. The source is restricted to the metric neighborhood where the
recovered exact power-cone identity holds. -/
theorem exists_pointChosen_classical_metric_transition
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, p ∈ F.source ∧ F p = 0 ∧
      (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y p / 2)
        (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
        (pointChosenSmoothRadialChart ha y p z)) ∧
      (∀ u ∈ F.source, ∀ v ∈ F.source,
        (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (F u) (F v)) ∧
      F.source ⊆ (pointChosenSmoothRadialChart ha y p).source := by
  let e := pointChosenSmoothRadialChart ha y p
  let α := coalescedPointExponent a y p / 2
  have hα : 0 ≤ α := div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  obtain ⟨R, hR, hep, hsource, hmetric⟩ := pointChosenSmoothRadialChart_power_metric_spec ha y p
  let U := {z : ℂ | (pointSmoothConformalEDist a y z p).toReal < R}
  have hU : IsOpen U := isOpen_lt (pointConformal_real_distance_continuous ha y p) continuous_const
  let eR := e.restrOpen U hU
  let F := eR.trans (coneRadialHomeomorph α hα).toOpenPartialHomeomorph
  have hFsource : F.source = e.source ∩ U := by simp [F, eR]
  have hF (z : ℂ) : F z = coneRadialEquiv α hα (e z) := rfl
  have hpU : p ∈ U := by
    change (pointSmoothConformalEDist a y p p).toReal < R
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR
  have hpE : p ∈ e.source := hsource p (by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le)
  refine ⟨F, by rw [hFsource]; exact ⟨hpE, hpU⟩, ?_, hF, ?_, ?_⟩
  · rw [hF, hep, coneRadialEquiv_zero]
  · intro u hu v hv
    rw [hFsource] at hu hv
    rw [hF, hF]
    change (pointSmoothConformalEDist a y u v).toReal =
      (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations
        ((coneRadialEquiv α hα).symm (coneRadialEquiv α hα (e u)))
        ((coneRadialEquiv α hα).symm (coneRadialEquiv α hα (e v)))).toReal
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hmetric u hu.2.le v hv.2.le]

  · intro z hz
    rw [hFsource] at hz
    exact hz.1

end RepulsiveCoulomb
