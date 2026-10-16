import LeanResearch.RepulsiveCoulomb.PointConeLargeAngle

/-! The inverse power map on the right half-plane, with exact physical length
transport. This will supply the Euclidean-chord competitor in a narrow sector. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointConeSectorInverse_hasDerivAt {α : ℝ} (hα : 0 ≤ α) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (pointConeSectorInverse α)
      ((((α + 1 : ℝ) : ℂ) * w) ^ (((α + 1 : ℝ) : ℂ)⁻¹ - 1)) w := by
  let n : ℂ := ((α + 1 : ℝ) : ℂ)
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast (show α + 1 ≠ 0 by linarith)
  have hs : n * w ∈ Complex.slitPlane := Or.inl (by
    simpa [n, Complex.mul_re] using mul_pos (show 0 < α + 1 by linarith) hw)
  have h := ((hasDerivAt_id w).const_mul n).cpow_const (c := n⁻¹) hs
  convert h using 1
  · rfl
  · change (n * w) ^ (n⁻¹ - 1) = n⁻¹ * (n * w) ^ (n⁻¹ - 1) * (n * 1)
    field_simp

theorem pointConeSectorInverse_analyticOnNhd {α : ℝ} (hα : 0 ≤ α) :
    AnalyticOnNhd ℂ (pointConeSectorInverse α) {w : ℂ | 0 < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro w hw
  exact (pointConeSectorInverse_hasDerivAt hα hw).differentiableAt.differentiableWithinAt

theorem pointConeSectorInverse_density_deriv {α : ℝ} (hα : 0 ≤ α) {w : ℂ} (hw : 0 < w.re) :
    pointConformalDensity (standardConeExponents α) standardConeLocations (pointConeSectorInverse α w) *
      ‖deriv (pointConeSectorInverse α) w‖ = 1 := by
  let v : ℂ := ((α + 1 : ℝ) : ℂ) * w
  have hv : v ≠ 0 := by
    have hvr : 0 < v.re := by
      simpa [v, Complex.mul_re] using mul_pos (show 0 < α + 1 by linarith) hw
    intro h
    simp [h] at hvr
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [standardCone_density, (pointConeSectorInverse_hasDerivAt hα hw).deriv]
  change ‖v ^ (((α + 1 : ℝ) : ℂ)⁻¹)‖ ^ α * ‖v ^ (((α + 1 : ℝ) : ℂ)⁻¹ - 1)‖ = 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_cpow_real, Complex.norm_cpow_real, ← Real.rpow_mul hvn.le,
    ← Real.rpow_add hvn]
  have he : (α + 1)⁻¹ * α + ((α + 1)⁻¹ - 1) = 0 := by
    field_simp
    ring
  rw [he, Real.rpow_zero]

end RepulsiveCoulomb
