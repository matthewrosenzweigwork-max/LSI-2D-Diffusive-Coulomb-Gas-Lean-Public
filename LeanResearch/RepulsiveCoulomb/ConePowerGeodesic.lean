import LeanResearch.RepulsiveCoulomb.ConeRadialGeodesic

/-! The exact power law for an apex geodesic in the original power-density
coordinate, as opposed to the intrinsic-radius classical cone coordinate. -/
noncomputable section
namespace RepulsiveCoulomb

theorem complexRadialPower_nonneg_smul {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) (z : ℂ) :
    complexRadialPower p (t • z) = t ^ p • complexRadialPower p z := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [complexRadialPower_zero, Real.zero_rpow hp.ne']
  · have he : t ^ (p - 1) * t = t ^ p := by
      rw [← Real.rpow_add_one ht.ne']
      congr 1
      ring
    unfold complexRadialPower
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      Real.mul_rpow ht.le (norm_nonneg z), smul_smul, smul_smul]
    congr 1
    calc
      t ^ (p - 1) * ‖z‖ ^ (p - 1) * t = (t ^ (p - 1) * t) * ‖z‖ ^ (p - 1) := by ring
      _ = _ := by rw [he]

theorem coneRadialEquiv_symm_nonneg_smul {α : ℝ} (hα : 0 ≤ α) {t : ℝ}
    (ht : 0 ≤ t) (w : ℂ) :
    (coneRadialEquiv α hα).symm (t • w) = t ^ (α + 1)⁻¹ • (coneRadialEquiv α hα).symm w := by
  change complexRadialPower (α + 1)⁻¹ ((α + 1) • (t • w)) = _
  rw [smul_comm (α + 1) t w,
    complexRadialPower_nonneg_smul (inv_pos.mpr (by linarith)) ht]
  rfl

theorem standardCone_geodesic_from_apex {α : ℝ} (hα : 0 < α)
    (γ : Set.Icc (0 : ℝ) 1 → ℂ) (w : ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = 0) (h1 : γ ⟨1, by norm_num⟩ = w)
    (hd : ∀ s t,
      (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (γ s) (γ t)).toReal =
        |t.1 - s.1| * coneRadialPotential α w) (t : Set.Icc (0 : ℝ) 1) :
    γ t = t.1 ^ (α + 1)⁻¹ • w := by
  let e := coneRadialIsometryEquiv α hα.le
  have hr : ∀ s u,
      @dist ℂ (classicalConeMetricSpace α hα.le).toDist (e (γ s)) (e (γ u)) =
        |u.1 - s.1| * ‖e w‖ := by
    intro s u
    change (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations
      ((coneRadialEquiv α hα.le).symm (coneRadialEquiv α hα.le (γ s)))
      ((coneRadialEquiv α hα.le).symm (coneRadialEquiv α hα.le (γ u)))).toReal = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hd]
    congr 1
    exact (coneRadialEquiv_norm α hα.le w).symm
  have heq := classicalCone_geodesic_from_apex hα (fun s => e (γ s)) (e w)
    (by rw [h0]; exact coneRadialEquiv_zero α hα.le) (by rw [h1]) hr t
  have h := congrArg (coneRadialEquiv α hα.le).symm heq
  change (coneRadialEquiv α hα.le).symm (coneRadialEquiv α hα.le (γ t)) =
    (coneRadialEquiv α hα.le).symm (t.1 • coneRadialEquiv α hα.le w) at h
  rw [Equiv.symm_apply_apply, coneRadialEquiv_symm_nonneg_smul hα.le t.2.1,
    Equiv.symm_apply_apply] at h
  exact h

end RepulsiveCoulomb
