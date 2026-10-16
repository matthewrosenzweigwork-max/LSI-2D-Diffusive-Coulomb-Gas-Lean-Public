module

public import LeanResearch.RepulsiveCoulomb.PointCutoffBump
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-! Unnormalized planar power-weight cutoff energy, for tensorized collision tubes. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem planar_power_cutoff_energy_integrable {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) :
    Integrable (fun u : ℂ => ‖u‖ ^ α * ‖gradient (pointCutoffBump 0 ε hε) u‖ ^ 2) := by
  have hc : Continuous (fun u : ℂ => ‖u‖ ^ α * ‖gradient (pointCutoffBump 0 ε hε) u‖ ^ 2) :=
    ((Real.continuous_rpow_const hα).comp continuous_norm).mul
      ((TauCeti.continuous_gradient_testFunction (pointCutoffTestFunction 0 ε hε)).norm.pow 2)
  have hs : HasCompactSupport (fun u : ℂ => ‖u‖ ^ α * ‖gradient (pointCutoffBump 0 ε hε) u‖ ^ 2) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * ε))
    intro u hu
    rw [pointCutoffBump_gradient_zero 0 ε hε hu]
    simp
  exact hc.integrable_of_hasCompactSupport hs

theorem planar_power_cutoff_energy_bound {α : ℝ} (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ) (hε : 0 < ε),
      (∫ u : ℂ, ‖u‖ ^ α * ‖gradient (pointCutoffBump 0 ε hε) u‖ ^ 2) ≤ K * ε ^ α := by
  obtain ⟨B, hB, hg⟩ := exists_pointCutoffBump_gradient_bound
  refine ⟨B ^ 2 * 2 ^ α * 4 * Real.pi, by positivity, ?_⟩
  intro ε hε
  let f : ℂ → ℝ := fun u => ‖u‖ ^ α * ‖gradient (pointCutoffBump 0 ε hε) u‖ ^ 2
  have hf (u : ℂ) : 0 ≤ f u := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have hb : ∀ u ∈ closedBall (0 : ℂ) (2 * ε), ‖f u‖ ≤ (2 * ε) ^ α * (B / ε) ^ 2 := by
    intro u hu
    have hn : ‖u‖ ≤ 2 * ε := by simpa only [mem_closedBall, dist_zero_right] using hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hf u)]
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hn hα)
      (pow_le_pow_left₀ (norm_nonneg _) (hg 0 ε hε u) 2) (sq_nonneg _) (by positivity)
  have hs : (∫ u in closedBall (0 : ℂ) (2 * ε), f u) = ∫ u, f u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    dsimp [f]
    rw [pointCutoffBump_gradient_zero 0 ε hε hu]
    simp
  have hi := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℂ)) (isCompact_closedBall (0 : ℂ) (2 * ε)).measure_lt_top hb
  rw [hs] at hi
  have hv : volume.real (closedBall (0 : ℂ) (2 * ε)) = (2 * ε) ^ 2 * Real.pi := by
    simp [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]
  rw [hv] at hi
  calc
    _ ≤ ‖∫ u, f u‖ := le_abs_self _
    _ ≤ _ := hi
    _ = _ := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) hε.le]
      field_simp
      ring

end RepulsiveCoulomb

