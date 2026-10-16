module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchObjectiveLSC
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

/-! Actual tightness and compactness of every finite objective sublevel. Moment
control is derived from the objective itself, and applies before a density or
finite second moment has been established. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem equilibriumObjective_sublevel_tight (β : ℝ) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    IsTightMeasureSet ((fun μ : ProbabilityMeasure ℂ => (μ : Measure ℂ)) ''
      {μ : ProbabilityMeasure ℂ | equilibriumNonnegativeObjective β μ ≤ C}) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let T : ℝ≥0∞ := 8 * (C + 1)
  have hT : T ≠ ∞ := by dsimp only [T]; finiteness
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nat_pos_inv_mul_lt hT hε.ne'
  refine ⟨closedBall (0 : ℂ) (Real.sqrt (n : ℝ)), isCompact_closedBall _ _, ?_⟩
  intro ξ hξ
  obtain ⟨μ, hμ, rfl⟩ := hξ
  have hmoment : (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≤ T :=
    (equilibriumObjective_secondMoment_bound β μ).trans
      (mul_le_mul_right (add_le_add hμ le_rfl) 8)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnT : (n : ℝ≥0∞) ≠ ∞ := by finiteness
  have hset : (closedBall (0 : ℂ) (Real.sqrt (n : ℝ)))ᶜ ⊆
      {x : ℂ | (n : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2)} := by
    intro x hx
    have hx' : Real.sqrt (n : ℝ) < ‖x‖ := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hr : (n : ℝ) ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    change (n : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hr
  calc
    (μ : Measure ℂ) (closedBall (0 : ℂ) (Real.sqrt (n : ℝ)))ᶜ ≤
        (μ : Measure ℂ) {x : ℂ | (n : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2)} := measure_mono hset
    _ ≤ (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) / n :=
      meas_ge_le_lintegral_div (by fun_prop) hn0 hnT
    _ = (n : ℝ≥0∞)⁻¹ * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) := by
      rw [ENNReal.div_eq_inv_mul]
    _ ≤ (n : ℝ≥0∞)⁻¹ * T := mul_le_mul_right hmoment _
    _ ≤ ε := hnε.le

/-- A finite sublevel is weakly compact on the full probability-measure space,
not only within a preselected density class. -/
theorem equilibriumObjective_sublevel_isCompact {β : ℝ} (hβ : 0 < β)
    {C : ℝ≥0∞} (hC : C ≠ ∞) :
    IsCompact {μ : ProbabilityMeasure ℂ | equilibriumNonnegativeObjective β μ ≤ C} := by
  have hc := isCompact_closure_of_isTightMeasureSet
    (S := {μ : ProbabilityMeasure ℂ | equilibriumNonnegativeObjective β μ ≤ C})
    (equilibriumObjective_sublevel_tight β hC)
  simpa only [(equilibriumObjective_sublevel_isClosed hβ C).closure_eq] using hc

end RepulsiveCoulomb
