import LeanResearch.RepulsiveCoulomb.ConeRadialGeodesic

/-! Actual local radial normal form for all constant-speed minimizing geodesics
issuing from a positive puncture. The cone chart and full metric disk are constructed,
not left as hypotheses. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_radial_geodesic_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ)
    (hp : 0 < coalescedPointExponent a y p) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ, 0 < r ∧ e p = 0 ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ r →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∀ t, e (γ t) = t.1 • e z ∧ γ t = e.symm (t.1 • e z) := by
  obtain ⟨e, r, hr, hep, hsource, _, hmetric⟩ := exists_pointConformal_classical_cone_disk ha y p
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ r := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hr.le
  refine ⟨e, r, hr, hep, ?_⟩
  intro z hz γ h0 h1 hd
  have hL : (pointSmoothConformalEDist a y p z).toReal = ‖e z‖ := by
    rw [pointSmoothConformalEDist_comm a y p z, hmetric z hz p hpp, hep,
      pointClassicalConeDist_apex]
  have hball (t : Icc (0 : ℝ) 1) : (pointSmoothConformalEDist a y (γ t) p).toReal ≤ r := by
    have h := hd t ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    have hbound : (pointSmoothConformalEDist a y p z).toReal ≤ r := by
      rwa [pointSmoothConformalEDist_comm a y p z]
    exact (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans hbound
  intro t
  have heq : e (γ t) = t.1 • e z := by
    apply classicalCone_geodesic_from_apex
      (show 0 < coalescedPointExponent a y p / 2 by positivity)
      (fun s => e (γ s)) (e z) (by rw [h0, hep]) (by rw [h1])
    intro s u
    change pointClassicalConeDist a y p (e (γ s)) (e (γ u)) = _
    rw [← hmetric (γ s) (hball s) (γ u) (hball u), hd, hL]
  exact ⟨heq, by rw [← heq, e.left_inv (hsource (hball t))]⟩

end RepulsiveCoulomb
