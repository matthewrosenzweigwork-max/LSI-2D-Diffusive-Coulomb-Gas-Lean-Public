import LeanResearch.RepulsiveCoulomb.PointGeodesicAtPuncture
import LeanResearch.RepulsiveCoulomb.ConePowerGeodesicNonnegative

/-! Uniform intrinsic-radius radial formulas at every point, including the
zero-exponent flat case. The metric chart and its whole disk are retained for
actual endpoint-sector constructions. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem classicalCone_geodesic_from_apex_nonneg {α : ℝ} (hα : 0 ≤ α)
    (γ : Icc (0 : ℝ) 1 → ℂ) (w : ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = 0) (h1 : γ ⟨1, by norm_num⟩ = w)
    (hd : ∀ s t, @dist ℂ (classicalConeMetricSpace α hα).toDist (γ s) (γ t) =
      |t.1 - s.1| * ‖w‖) (t : Icc (0 : ℝ) 1) :
    γ t = t.1 • w := by
  rcases hα.eq_or_lt with he | hα
  · subst α
    have hdist (s u : Icc (0 : ℝ) 1) : dist (γ s) (γ u) = |u.1 - s.1| * ‖w‖ := by
      have h := hd s u
      rw [classicalCone_zero_dist] at h
      simpa only [dist_eq_norm'] using h
    have hs := hdist ⟨0, by norm_num⟩ t
    have hu := hdist t ⟨1, by norm_num⟩
    rw [h0, sub_zero, abs_of_nonneg t.2.1] at hs
    rw [h1, abs_of_nonneg (sub_nonneg.mpr t.2.2)] at hu
    have heq := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
      (x := (0 : ℂ)) (y := γ t) (z := w) (r := t.1)
      (by simpa only [dist_zero_left] using hs)
      (by simpa only [dist_zero_left] using hu)
    simpa only [AffineMap.lineMap_apply_module, smul_zero, zero_add] using heq
  · exact classicalCone_geodesic_from_apex hα γ w h0 h1 hd t

/-- A full constructed metric disk, plus the radial formula for every exact
geodesic issuing from its center. No positive puncture assumption remains. -/
theorem exists_pointConformal_radial_metric_disk {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R : ℝ, 0 < R ∧ e p = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ R} ⊆ e.source ∧
      (∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (e u) (e v)) ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ R →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∀ t, e (γ t) = t.1 • e z := by
  obtain ⟨e, R, hR, hep, hsource, _, hmetric⟩ :=
    exists_pointConformal_classical_cone_disk ha y p
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  refine ⟨e, R, hR, hep, hsource, hmetric, ?_⟩
  intro z hz γ h0 h1 hd
  have hL : (pointSmoothConformalEDist a y p z).toReal = ‖e z‖ := by
    rw [pointSmoothConformalEDist_comm a y p z, hmetric z hz p hpp, hep,
      pointClassicalConeDist_apex]
  have hball (t : Icc (0 : ℝ) 1) :
      (pointSmoothConformalEDist a y (γ t) p).toReal ≤ R := by
    have h := hd t ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    have hbound : (pointSmoothConformalEDist a y p z).toReal ≤ R := by
      rwa [pointSmoothConformalEDist_comm a y p z]
    exact (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans hbound
  intro t
  apply classicalCone_geodesic_from_apex_nonneg (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
    (fun s => e (γ s)) (e z) (by rw [h0, hep]) (by rw [h1])
  intro s u
  change pointClassicalConeDist a y p (e (γ s)) (e (γ u)) = _
  rw [← hmetric (γ s) (hball s) (γ u) (hball u), hd, hL]

end RepulsiveCoulomb
