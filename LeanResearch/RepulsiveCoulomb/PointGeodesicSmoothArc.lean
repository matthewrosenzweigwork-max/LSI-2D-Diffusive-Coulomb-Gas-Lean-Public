import LeanResearch.RepulsiveCoulomb.PointGeodesicRegularArc
import LeanResearch.RepulsiveCoulomb.AnalyticArcSmoothExtension

/-! Globally smooth regular Euclidean arc representatives for every short
nonconstant point-conformal geodesic, including arcs issuing from punctures. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_geodesic_smooth_arc_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ≠ p →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∃ η : ℝ → ℂ,
            ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
            InjOn η (Icc (0 : ℝ) 1) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, deriv η s ≠ 0) ∧
            η 0 = p ∧ η 1 = z ∧
            (∀ t : Icc (0 : ℝ) 1,
              γ t = η (t.1 ^ (coalescedPointExponent a y p / 2 + 1)⁻¹)) ∧
            Set.range γ = η '' Icc (0 : ℝ) 1 := by
  obtain ⟨R, hR, hlocal⟩ := exists_pointConformal_geodesic_regular_arc_radius ha y p
  refine ⟨R, hR, ?_⟩
  intro z hz hzp γ h0 h1 hd
  obtain ⟨η, hA, hinj, hderiv, he0, he1, hparam, himage⟩ := hlocal z hz hzp γ h0 h1 hd
  obtain ⟨g, hg, hagree⟩ := analytic_unitInterval_global_smooth_extension η hA
  have heq : EqOn g η (Icc (0 : ℝ) 1) := fun t ht => (hagree t ht).self_of_nhds
  refine ⟨g, hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact hinj hs ht ((heq hs).symm.trans (hst.trans (heq ht)))
  · intro t ht
    rw [(hagree t ht).deriv_eq]
    exact hderiv t ht
  · rw [heq (by norm_num)]
    exact he0
  · rw [heq (by norm_num)]
    exact he1
  · intro t
    rw [heq ⟨Real.rpow_nonneg t.2.1 _, Real.rpow_le_one t.2.1 t.2.2
      (inv_nonneg.mpr (by have := coalescedPointExponent_nonneg a y p; linarith))⟩]
    exact hparam t
  · rw [himage]
    exact heq.image_eq.symm

end RepulsiveCoulomb
