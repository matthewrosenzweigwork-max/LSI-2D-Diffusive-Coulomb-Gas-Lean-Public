import LeanResearch.RepulsiveCoulomb.PointActualBigonExclusion
import LeanResearch.RepulsiveCoulomb.PointGeodesicJordanBigon

/-! Global uniqueness of the actual exact metric segment. Disagreement of
two minimizing segments constructs a genuine simple bigon, now excluded by
the actual source-instantiated Gauss--Bonnet theorem. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointConformal_geodesic_unique
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (p q : ℂ) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal) : γ₁ = γ₂ := by
  by_cases hpq : p = q
  · rw [← hpq] at hd₁ hd₂
    exact (pointConformal_geodesic_constant ha y p γ₁ h10 hd₁).trans
      (pointConformal_geodesic_constant ha y p γ₂ h20 hd₂).symm
  · by_contra hne
    obtain ⟨u, v, huv, δ₁, δ₂, hδ10, hδ11, hδ20, hδ21, hδ₁, hδ₂, hmeet, _⟩ :=
      exists_pointConformal_jordan_geodesic_bigon ha y hpq γ₁ γ₂ h10 h11 h20 h21 hd₁ hd₂ hne
    exact not_pointConformal_simple_geodesic_bigon ha y huv δ₁ δ₂
      hδ10 hδ11 hδ20 hδ21 hδ₁ hδ₂ hmeet

end RepulsiveCoulomb
