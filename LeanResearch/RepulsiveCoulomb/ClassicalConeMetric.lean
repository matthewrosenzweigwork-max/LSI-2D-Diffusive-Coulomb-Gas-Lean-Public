import LeanResearch.RepulsiveCoulomb.ComplexRadialPower

/-! Classical Euclidean cone in complex polar coordinates. The coordinate's
ordinary modulus is the intrinsic apex radius; its argument is multiplied by
alpha+1, giving total angle 2*pi*(alpha+1). The metric is transported from the
proved power-density model, and its explicit classical cosine formula is proved
below. Thus the triangle inequality is not assumed for a raw formula. -/
noncomputable section
open scoped ENNReal
namespace RepulsiveCoulomb

@[instance_reducible] def standardConeMetricSpace (α : ℝ) (hα : 0 ≤ α) : MetricSpace ℂ :=
  pointSmoothConformalMetricSpace (a := standardConeExponents α)
    (fun j ↦ by dsimp [standardConeExponents]; positivity) standardConeLocations

@[instance_reducible] def classicalConeMetricSpace (α : ℝ) (hα : 0 ≤ α) : MetricSpace ℂ :=
  MetricSpace.induced (coneRadialEquiv α hα).symm (coneRadialEquiv α hα).symm.injective
    (standardConeMetricSpace α hα)

def coneRadialIsometryEquiv (α : ℝ) (hα : 0 ≤ α) :
    @IsometryEquiv ℂ ℂ (standardConeMetricSpace α hα).toPseudoEMetricSpace
      (classicalConeMetricSpace α hα).toPseudoEMetricSpace :=
  @IsometryEquiv.mk ℂ ℂ (standardConeMetricSpace α hα).toPseudoEMetricSpace
    (classicalConeMetricSpace α hα).toPseudoEMetricSpace (coneRadialEquiv α hα) (by
    intro x z
    change pointSmoothConformalEDist (standardConeExponents α) standardConeLocations
      ((coneRadialEquiv α hα).symm (coneRadialEquiv α hα x))
      ((coneRadialEquiv α hα).symm (coneRadialEquiv α hα z)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl)

theorem classicalCone_distance_formula {α : ℝ} (hα : 0 < α) (x z : ℂ) :
    @dist ℂ (classicalConeMetricSpace α hα.le).toDist x z =
      Real.sqrt (‖x‖ ^ 2 + ‖z‖ ^ 2 - 2 * ‖x‖ * ‖z‖ *
        Real.cos (min Real.pi ((α + 1) * |Complex.arg (z / x)|))) := by
  let e := coneRadialEquiv α hα.le
  have hr (w : ℂ) : coneRadialPotential α (e.symm w) = ‖w‖ := by
    rw [← coneRadialEquiv_norm α hα.le, Equiv.apply_symm_apply]
  have ha : Complex.arg (e.symm z / e.symm x) = Complex.arg (z / x) := by
    have h := coneRadialEquiv_arg_div α hα.le (e.symm x) (e.symm z)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  change (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (e.symm x) (e.symm z)).toReal = _
  rw [standardCone_distance_formula hα, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hr, hr, ha]

theorem classicalCone_zero_dist (x z : ℂ) :
    @dist ℂ (classicalConeMetricSpace 0 le_rfl).toDist x z = ‖z - x‖ := by
  change (pointSmoothConformalEDist (standardConeExponents 0) standardConeLocations
    ((coneRadialEquiv 0 le_rfl).symm x) ((coneRadialEquiv 0 le_rfl).symm z)).toReal = _
  have he (w : ℂ) : (coneRadialEquiv 0 le_rfl).symm w = w := by
    change complexRadialPower (0 + 1)⁻¹ ((0 + 1) • w) = w
    simp [complexRadialPower_one]
  rw [he, he, standardCone_zero_distance, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem classicalCone_dist_apex (α : ℝ) (hα : 0 ≤ α) (w : ℂ) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist w 0 = ‖w‖ := by
  let e := coneRadialEquiv α hα
  have h0 : e.symm 0 = 0 := by
    apply e.injective
    rw [Equiv.apply_symm_apply, coneRadialEquiv_zero]
  have hr : coneRadialPotential α (e.symm w) = ‖w‖ := by
    rw [← coneRadialEquiv_norm α hα, Equiv.apply_symm_apply]
  change (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (e.symm w) (e.symm 0)).toReal = _
  rw [h0, pointSmoothConformalEDist_comm (standardConeExponents α) standardConeLocations (e.symm w) 0,
    standardCone_distance_from_apex_nonneg hα, ENNReal.toReal_ofReal (by positivity)]
  simpa [coneRadialPotential, div_eq_mul_inv, mul_comm] using hr

end RepulsiveCoulomb
