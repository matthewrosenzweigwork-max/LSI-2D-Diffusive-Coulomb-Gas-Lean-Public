module

public import LeanResearch.RepulsiveCoulomb.HolomorphicDiskL2

@[expose] public section

/-! Actual planar scaling for the local holomorphic L2 evaluation estimate. -/
noncomputable section
open Set MeasureTheory Metric
namespace RepulsiveCoulomb

theorem complex_closedBall_integral_affine (f : ℂ → ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z in closedBall c (2 * r), f z) = r ^ 2 * ∫ z in closedBall (0 : ℂ) 2, f (c + r • z) := by
  let g : ℂ → ℝ := (closedBall c (2 * r)).indicator f
  have hmem (z : ℂ) : c + r • z ∈ closedBall c (2 * r) ↔ z ∈ closedBall (0 : ℂ) 2 := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor <;> intro h <;> nlinarith
  have he (z : ℂ) : g (c + r • z) =
      (closedBall (0 : ℂ) 2).indicator (fun w => f (c + r • w)) z := by
    by_cases hz : z ∈ closedBall (0 : ℂ) 2
    · simp only [g, Set.indicator_of_mem hz, Set.indicator_of_mem ((hmem z).mpr hz)]
    · simp only [g, Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (fun h => hz ((hmem z).mp h))]
  have hi := complex_integral_affine g c hr
  simp_rw [he] at hi
  rw [integral_indicator isClosed_closedBall.measurableSet] at hi
  change (∫ z in closedBall (0 : ℂ) 2, f (c + r • z)) =
    (r ^ 2)⁻¹ * ∫ z, (closedBall c (2 * r)).indicator f z at hi
  rw [integral_indicator isClosed_closedBall.measurableSet] at hi
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  field_simp at hi
  simpa only [mul_comm] using hi.symm

theorem holomorphic_disk_integral_lower {f : ℂ → ℂ} (hc : Continuous f)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c (2 * r))) :
    (2 * Real.pi) * r ^ 2 * ‖f c‖ ^ 2 ≤ ∫ z in closedBall c (2 * r), ‖f z‖ ^ 2 := by
  have hmap : ∀ z ∈ ball (0 : ℂ) 2, c + r • z ∈ ball c (2 * r) := by
    intro z hz
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hz ⊢
    nlinarith
  have hd : Differentiable ℂ (fun z : ℂ => c + r • z) :=
    (differentiable_const c).add (differentiable_id.const_smul r)
  have h := holomorphic_disk_two_integral_lower (hc.comp (by fun_prop))
    (hf.comp hd.differentiableOn hmap)
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg r)
  rw [complex_closedBall_integral_affine _ c hr]
  simp only [Function.comp_apply, smul_zero, add_zero] at hh
  convert hh using 1 <;> ring

end RepulsiveCoulomb
