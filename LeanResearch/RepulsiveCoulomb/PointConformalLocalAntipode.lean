import LeanResearch.RepulsiveCoulomb.ConeGeodesicAngle

/-! Every intrinsic direction has an actual equally distant antipode in a
constructed small point-metric disk. This supplies local extendibility through
all cone vertices. Global minimizing continuation is a separate theorem. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem classicalCone_antipodal_distance {α : ℝ} (hα : 0 ≤ α) (u : ℂ) :
    @dist ℂ (classicalConeMetricSpace α hα).toDist u (-u) = 2 * ‖u‖ := by
  rcases hα.eq_or_lt with hzero | hpos
  · subst α
    rw [classicalCone_zero_dist, show (-u) - u = -(u + u) by abel,
      norm_neg, ← two_smul ℝ u, norm_smul]
    norm_num
  · by_cases hu : u = 0
    · subst u
      simp only [neg_zero, norm_zero, mul_zero]
      exact (classicalConeMetricSpace α hα).dist_self 0
    have hv : -u ≠ 0 := neg_ne_zero.mpr hu
    have hangle : Real.pi ≤ (α + 1) * |Complex.arg ((-u) / u)| := by
      rw [neg_div, div_self hu, Complex.arg_neg_one, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    rw [(classicalCone_apex_triangle_eq_iff hpos hu hv).mpr hangle, norm_neg]
    ring

/-- For every point and every nearby endpoint, construct the opposite endpoint
with exact doubled ambient distance. The disk and antipode are not inputs. -/
theorem exists_pointConformal_local_antipodes {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℂ,
      (pointSmoothConformalEDist a y u p).toReal ≤ R →
      ∃ v : ℂ, (pointSmoothConformalEDist a y v p).toReal =
          (pointSmoothConformalEDist a y u p).toReal ∧
        (pointSmoothConformalEDist a y u v).toReal =
          2 * (pointSmoothConformalEDist a y u p).toReal := by
  obtain ⟨e, R, hR, hep, hsource, hbij, hmetric⟩ :=
    exists_pointConformal_classical_cone_disk ha y p
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  refine ⟨R, hR, ?_⟩
  intro u hu
  have huNorm : (pointSmoothConformalEDist a y u p).toReal = ‖e u‖ := by
    rw [hmetric u hu p hpp, hep, pointClassicalConeDist_apex]
  have hneg : ‖-e u‖ ≤ R := by rw [norm_neg, ← huNorm]; exact hu
  obtain ⟨v, hv, hev⟩ := hbij.surjOn hneg
  refine ⟨v, ?_, ?_⟩
  · rw [hmetric v hv p hpp, hep, pointClassicalConeDist_apex, hev, norm_neg, huNorm]
  · rw [hmetric u hu v hv, hev, huNorm]
    exact classicalCone_antipodal_distance
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) (e u)

end RepulsiveCoulomb
