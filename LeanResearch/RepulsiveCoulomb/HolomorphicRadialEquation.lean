import LeanResearch.RepulsiveCoulomb.HolomorphicRadialAverage

/-! The exact regular-singular differential identity for the weighted radial
average. It is proved by the fundamental theorem of calculus, not assumed. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology Interval
namespace RepulsiveCoulomb

theorem holomorphicRadialAverage_analyticOnNhd {α : ℝ} (hα : 0 ≤ α) (p : ℂ)
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (ball p R)) :
    AnalyticOnNhd ℂ (holomorphicRadialAverage α p g) (ball p (R / 2)) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro z hz
  exact (holomorphicRadialAverage_hasDerivAt hα p hR hg hz).differentiableAt.differentiableWithinAt

theorem holomorphicRadialAverage_equation {α : ℝ} (hα : 0 ≤ α) (p : ℂ)
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (ball p R))
    {z : ℂ} (hz : z ∈ ball p (R / 2)) :
    ((α + 1 : ℝ) : ℂ) * holomorphicRadialAverage α p g z +
      (z - p) * deriv (holomorphicRadialAverage α p g) z = ((α + 1 : ℝ) : ℂ) * g z := by
  let T : ℝ → ℂ := fun t ↦ p + t • (z - p)
  have hmap : MapsTo T (Icc (0 : ℝ) 1) (ball p R) := by
    intro t ht
    exact (closedBall_subset_ball (by linarith : R / 2 < R))
      (radialSegment_mem_closedBall (ball_subset_closedBall hz) ht)
  have hgc : ContinuousOn (g ∘ T) (Icc (0 : ℝ) 1) := hg.continuousOn.comp (by fun_prop) hmap
  have hdc : ContinuousOn (deriv g ∘ T) (Icc (0 : ℝ) 1) := hg.deriv.continuousOn.comp (by fun_prop) hmap
  let F : ℝ → ℂ := fun t ↦ t ^ α • g (T t)
  let D : ℝ → ℂ := fun t ↦ t ^ α • ((t : ℂ) * deriv g (T t))
  let H : ℝ → ℂ := fun t ↦ t ^ (α + 1) • g (T t)
  have hcF : ContinuousOn F (Icc (0 : ℝ) 1) := (Real.continuous_rpow_const hα).continuousOn.smul hgc
  have hcD : ContinuousOn D (Icc (0 : ℝ) 1) :=
    (Real.continuous_rpow_const hα).continuousOn.smul (Complex.continuous_ofReal.continuousOn.mul hdc)
  have hcH : ContinuousOn H (Icc (0 : ℝ) 1) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ α + 1)).continuousOn.smul hgc
  have hFint : IntervalIntegrable F volume 0 1 := hcF.intervalIntegrable_of_Icc zero_le_one
  have hDint : IntervalIntegrable D volume 0 1 := hcD.intervalIntegrable_of_Icc zero_le_one
  have hdiff (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt H ((α + 1) • F t + (z - p) * D t) t := by
    have hlin : HasDerivAt T (z - p) t := by
      simpa [T] using ((hasDerivAt_id t).smul_const (z - p)).const_add p
    have hfg := (hg (T t) (hmap ⟨ht.1.le, ht.2.le⟩)).differentiableAt
    have hcomp : HasDerivAt (fun t ↦ g (T t)) ((z - p) * deriv g (T t)) t := by
      convert (hfg.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hlin using 1
      · rfl
      · change (z - p) * deriv g (T t) = (fderiv ℂ g (T t)) (z - p)
        rw [fderiv_eq_smul_deriv, smul_eq_mul]
    have hp := (Real.hasDerivAt_rpow_const (x := t) (p := α + 1) (Or.inl ht.1.ne')).smul hcomp
    convert hp using 1
    have hpow : t ^ (α + 1) = t ^ α * t := by rw [Real.rpow_add ht.1, Real.rpow_one]
    simp only [F, D, show α + 1 - 1 = α by ring, hpow, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcH hdiff
    ((hFint.smul (α + 1)).add (hDint.const_mul (z - p)))
  rw [intervalIntegral.integral_add (f := fun t ↦ (α + 1) • F t)
      (g := fun t ↦ (z - p) * D t) (hFint.smul (α + 1)) (hDint.const_mul (z - p)),
    intervalIntegral.integral_smul, intervalIntegral.integral_const_mul] at he
  have hα1 : α + 1 ≠ 0 := by linarith
  have heq : (α + 1) • (∫ t in (0 : ℝ)..1, F t) +
      (z - p) * (∫ t in (0 : ℝ)..1, D t) = g z := by
    simpa [H, T, Real.zero_rpow hα1] using he
  rw [(holomorphicRadialAverage_hasDerivAt hα p hR hg hz).deriv]
  change ((α + 1 : ℝ) : ℂ) * ((α + 1) • (∫ t in (0 : ℝ)..1, F t)) +
      (z - p) * ((α + 1) • (∫ t in (0 : ℝ)..1, D t)) = _
  have hm := congrArg (fun w : ℂ ↦ ((α + 1 : ℝ) : ℂ) * w) heq
  simp only [Complex.real_smul] at hm ⊢
  linear_combination hm

end RepulsiveCoulomb
