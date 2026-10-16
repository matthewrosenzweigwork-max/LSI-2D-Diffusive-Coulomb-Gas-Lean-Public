import LeanResearch.RepulsiveCoulomb.ConePowerGeodesic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween

/-! Include the flat alpha=0 case in the exact cone geodesic power law. -/
noncomputable section
namespace RepulsiveCoulomb

theorem standardCone_geodesic_from_apex_nonneg {α : ℝ} (hα : 0 ≤ α)
    (γ : Set.Icc (0 : ℝ) 1 → ℂ) (w : ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = 0) (h1 : γ ⟨1, by norm_num⟩ = w)
    (hd : ∀ s t,
      (pointSmoothConformalEDist (standardConeExponents α) standardConeLocations (γ s) (γ t)).toReal =
        |t.1 - s.1| * coneRadialPotential α w) (t : Set.Icc (0 : ℝ) 1) :
    γ t = t.1 ^ (α + 1)⁻¹ • w := by
  rcases hα.eq_or_lt with he | hα
  · subst α
    have hdist (s u : Set.Icc (0 : ℝ) 1) : dist (γ s) (γ u) = |u.1 - s.1| * ‖w‖ := by
      have h := hd s u
      rw [standardCone_zero_distance, ENNReal.toReal_ofReal (norm_nonneg _)] at h
      simpa only [coneRadialPotential, zero_add, Real.rpow_one, div_one, inv_one, one_mul, dist_eq_norm'] using h
    have hs := hdist ⟨0, by norm_num⟩ t
    have hu := hdist t ⟨1, by norm_num⟩
    rw [h0, sub_zero, abs_of_nonneg t.2.1] at hs
    rw [h1, abs_of_nonneg (sub_nonneg.mpr t.2.2)] at hu
    have heq := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
      (x := (0 : ℂ)) (y := γ t) (z := w) (r := t.1)
      (by simpa only [dist_zero_left] using hs)
      (by simpa only [dist_zero_left] using hu)
    simpa only [zero_add, inv_one, Real.rpow_one, AffineMap.lineMap_apply_module,
      smul_zero, zero_add] using heq
  · exact standardCone_geodesic_from_apex hα γ w h0 h1 hd t

end RepulsiveCoulomb
