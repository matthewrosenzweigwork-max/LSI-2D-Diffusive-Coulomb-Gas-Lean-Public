import LeanResearch.RepulsiveCoulomb.PointConeBarrierDerivative

/-! The cone support profile is genuinely C1 across the apex, with the sharp
weighted gradient bound and hence a global intrinsic distance lower bound. -/
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coneAngularBarrier_hasFDerivAt_zero {α : ℝ} (hα : 0 < α) :
    HasFDerivAt (coneAngularBarrier α) (0 : ℂ →L[ℝ] ℝ) 0 := by
  have hr : HasFDerivAt (coneRadialPotential α) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h := ((coneRadialPotential_contDiff hα).differentiable one_ne_zero 0).hasFDerivAt
    have hz : fderiv ℝ (coneRadialPotential α) 0 = 0 := by
      apply norm_eq_zero.mp
      rw [coneRadialPotential_norm_fderiv hα, norm_zero, Real.zero_rpow hα.ne']
    rwa [hz] at h
  have hlo : (coneRadialPotential α) =o[𝓝 (0 : ℂ)] (fun z ↦ z) := by
    change (fun z : ℂ ↦ (α + 1)⁻¹ * ‖z‖ ^ (α + 1)) =o[𝓝 (0 : ℂ)] (fun z ↦ z)
    simpa [coneRadialPotential, Real.zero_rpow (show α + 1 ≠ 0 by linarith)] using hr.isLittleO
  apply HasFDerivAt.of_isLittleO
  simp only [coneAngularBarrier_zero hα, sub_zero, zero_apply]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [hlo.bound hc] with z hz
  apply le_trans _ hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ coneRadialPotential α z by
    unfold coneRadialPotential; positivity)]
  simpa [coneRadialPotential, div_eq_mul_inv, mul_comm] using coneAngularBarrier_abs_le hα z

theorem coneAngularBarrier_norm_fderiv {α : ℝ} (hα : 0 < α) (z : ℂ) :
    ‖fderiv ℝ (coneAngularBarrier α) z‖ ≤ ‖z‖ ^ α := by
  by_cases hz : z = 0
  · subst z
    rw [(coneAngularBarrier_hasFDerivAt_zero hα).fderiv, norm_zero]
    positivity
  · exact coneAngularBarrier_norm_fderiv_ne_zero hα hz

theorem coneAngularBarrier_contDiff {α : ℝ} (hα : 0 < α) :
    ContDiff ℝ 1 (coneAngularBarrier α) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨?_, continuous_iff_continuousAt.mpr ?_⟩
  · intro z
    by_cases hz : z = 0
    · subst z
      exact (coneAngularBarrier_hasFDerivAt_zero hα).differentiableAt
    · exact (coneAngularBarrier_contDiffAt_ne_zero hα hz).differentiableAt one_ne_zero
  · intro z
    by_cases hz : z = 0
    · subst z
      rw [ContinuousAt, (coneAngularBarrier_hasFDerivAt_zero hα).fderiv,
        tendsto_zero_iff_norm_tendsto_zero]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
        (fun _ ↦ norm_nonneg _) (coneAngularBarrier_norm_fderiv hα)
      have hc : ContinuousAt (fun w : ℂ ↦ ‖w‖ ^ α) 0 :=
        continuousAt_id.norm.rpow_const (Or.inr hα.le)
      simpa [ContinuousAt, Real.zero_rpow hα.ne'] using hc
    · exact (coneAngularBarrier_contDiffAt_ne_zero hα hz).continuousAt_fderiv one_ne_zero

theorem coneAngularBarrier_metric_lower {α : ℝ} (hα : 0 < α) (x z : ℂ) :
    ENNReal.ofReal |coneAngularBarrier α z - coneAngularBarrier α x| ≤
      pointSmoothConformalEDist (standardConeExponents α) standardConeLocations x z := by
  have hd : ∀ w : ℂ, ‖fderiv ℝ (coneAngularBarrier α) w‖ ≤
      1 * pointConformalDensity (standardConeExponents α) standardConeLocations w := by
    intro w
    simpa only [one_mul, standardCone_density] using coneAngularBarrier_norm_fderiv hα w
  simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_one, one_mul] using
    pointConformal_metric_barrier (standardConeExponents α) standardConeLocations
      (coneAngularBarrier_contDiff hα) zero_lt_one hd x z

end RepulsiveCoulomb
