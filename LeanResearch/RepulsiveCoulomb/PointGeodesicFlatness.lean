module

public import Mathlib.Analysis.InnerProductSpace.Convex
public import LeanResearch.RepulsiveCoulomb.PointConformalGeodesicArc
public import LeanResearch.RepulsiveCoulomb.PointConformalMetricCharts
public import Mathlib.Analysis.Convex.StrictConvexBetween

@[expose] public section

/-! Two actual local facts needed for the geometric continuation: nonconstant
geodesics meet the finite puncture set only finitely often, and a minimizing
passage in a flat chart lies on the Euclidean straight segment. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem pointConformal_geodesic_puncture_times_finite {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal) :
    (γ ⁻¹' pointPunctures a y).Finite :=
  (pointPunctures_finite a y).preimage
    (pointConformal_geodesic_injective ha y hxz γ hd).injOn

theorem pointConformal_geodesic_additive {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {x z : ℂ} (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    {s t u : Icc (0 : ℝ) 1} (hst : s ≤ t) (htu : t ≤ u) :
    (pointSmoothConformalEDist a y (γ s) (γ u)).toReal =
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal +
        (pointSmoothConformalEDist a y (γ t) (γ u)).toReal := by
  change s.1 ≤ t.1 at hst
  change t.1 ≤ u.1 at htu
  rw [hd, hd, hd, abs_of_nonneg (sub_nonneg.mpr (hst.trans htu)),
    abs_of_nonneg (sub_nonneg.mpr hst), abs_of_nonneg (sub_nonneg.mpr htu)]
  ring

theorem exists_pointConformal_flat_straight_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ, 0 < r ∧ e p = 0 ∧ ball p r ⊆ e.source ∧
      ∀ u ∈ ball p r, ∀ v ∈ ball p r, ∀ w ∈ ball p r,
        (pointSmoothConformalEDist a y u w).toReal =
          (pointSmoothConformalEDist a y u v).toReal +
            (pointSmoothConformalEDist a y v w).toReal →
        Wbtw ℝ (e u) (e v) (e w) := by
  obtain ⟨e, r, hr, hep, hsub, hd⟩ := exists_pointConformal_flat_metric_chart ha y hp
  have hd' (u : ℂ) (hu : u ∈ ball p r) (v : ℂ) (hv : v ∈ ball p r) :
      (pointSmoothConformalEDist a y u v).toReal = dist (e u) (e v) := by
    rw [hd u hu v hv, ENNReal.toReal_ofReal (norm_nonneg _), dist_eq_norm']
  refine ⟨e, r, hr, hep, hsub, ?_⟩
  intro u hu v hv w hw hmin
  rw [hd' u hu w hw, hd' u hu v hv, hd' v hv w hw] at hmin
  exact dist_add_dist_eq_iff.mp hmin.symm

end RepulsiveCoulomb
