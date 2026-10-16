import LeanResearch.RepulsiveCoulomb.DbarBranchProperMetricCutoff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Exact derivative and actual O(1/R) metric-dual bound for the proper
cutoffs. This supplies the cutoff coefficient bound; it does not by itself
prove cutoff stability or approximation in the joint adjoint/compatibility domain. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem dbarUnitCutoff_derivative_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv (dbarUnitCutoff : ℝ → ℝ) t| ≤ C := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (dbarUnitCutoff : ℝ → ℝ) := dbarUnitCutoff.contDiff
  obtain ⟨C, hC⟩ := (hc.continuous_deriv (by simp)).bounded_above_of_compact_support
    dbarUnitCutoff.hasCompactSupport.deriv
  refine ⟨C, (norm_nonneg _).trans (hC 0), ?_⟩
  intro t
  simpa only [Real.norm_eq_abs] using hC t

theorem coulombMetricCutoff_fderiv {N : ℕ} (R : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    fderiv ℝ (coulombMetricCutoff (N := N) R) z =
      (deriv (dbarUnitCutoff : ℝ → ℝ) (coulombGraphRadius z / R) / R) •
        fderiv ℝ (coulombGraphRadius (N := N)) z := by
  classical
  have hc : ContDiff ℝ (⊤ : ℕ∞) (dbarUnitCutoff : ℝ → ℝ) := dbarUnitCutoff.contDiff
  have hρ := ((coulombGraphRadius_contDiffAt hz).differentiableAt (by simp)).hasFDerivAt
  have hscaled : HasFDerivAt (fun w : CoulombConfig N => coulombGraphRadius w / R)
      (R⁻¹ • fderiv ℝ (coulombGraphRadius (N := N)) z) z := by
    simpa only [div_eq_mul_inv, mul_comm] using hρ.const_mul R⁻¹
  have houter := ((hc.differentiable (by simp)) (coulombGraphRadius z / R)).hasDerivAt.comp_hasFDerivAt z hscaled
  have he : coulombMetricCutoff (N := N) R =ᶠ[𝓝 z]
      fun w => dbarUnitCutoff (coulombGraphRadius w / R) := by
    filter_upwards [(coulombDomain N).isOpen.mem_nhds hz] with w hw
    exact indicator_of_mem hw _
  have hd := (houter.congr_of_eventuallyEq he).fderiv
  simpa only [smul_smul, div_eq_mul_inv] using hd

theorem coulombMetricCutoff_metric_dual_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {R : ℝ}, 0 < R → ∀ z ∈ coulombDomain N,
      ‖(fderiv ℝ (coulombMetricCutoff (N := N) R) z).comp
        ((dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))).restrictScalars ℝ)‖ ≤ C / R := by
  obtain ⟨C, hC, hder⟩ := dbarUnitCutoff_derivative_bounded
  refine ⟨C, hC, ?_⟩
  intro N R hR z hz
  let B : CoulombConfig N →L[ℝ] CoulombConfig N :=
    (dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))).restrictScalars ℝ
  have he : (fderiv ℝ (coulombMetricCutoff (N := N) R) z).comp B =
      (deriv (dbarUnitCutoff : ℝ → ℝ) (coulombGraphRadius z / R) / R) •
        ((fderiv ℝ (coulombGraphRadius (N := N)) z).comp B) := by
    rw [coulombMetricCutoff_fderiv R hz]
    ext v
    rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hR]
  calc
    _ ≤ (|deriv (dbarUnitCutoff : ℝ → ℝ) (coulombGraphRadius z / R)| / R) * 1 :=
      mul_le_mul_of_nonneg_left (coulombGraphRadius_metric_dual_bound hz) (by positivity)
    _ ≤ C / R := by rw [mul_one]; exact div_le_div_of_nonneg_right (hder _) hR.le

theorem coulombMetricCutoff_tendsto_one {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    Tendsto (fun R : ℝ => coulombMetricCutoff R z) atTop (𝓝 1) := by
  have he : (fun R : ℝ => coulombMetricCutoff R z) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (coulombGraphRadius z + 1)] with R hR
    exact coulombMetricCutoff_eq_one (by linarith [coulombGraphRadius_pos z]) hz (by linarith)
  exact tendsto_const_nhds.congr' he.symm

end RepulsiveCoulomb
