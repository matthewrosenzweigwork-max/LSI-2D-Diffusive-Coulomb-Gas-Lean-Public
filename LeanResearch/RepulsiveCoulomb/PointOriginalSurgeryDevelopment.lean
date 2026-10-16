module

public import LeanResearch.RepulsiveCoulomb.PointFiniteSurgeryMetricCharts
public import LeanResearch.RepulsiveCoulomb.PointSurgeryIncidentOverlap
public import LeanResearch.RepulsiveCoulomb.FlatAtlasLengthGlobalization

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Join original finite allocation, all actual local
surgery charts, actual seam-overlap rigidity, constructed global development,
and constructed complete intrinsic pullback length metric. The only original
inputs are nonnegative coefficients and their locations. No atlas, developing
map, metric completeness or path-independence certificate is supplied. -/
noncomputable section
open Set Filter
open scoped Topology
open scoped NNReal
namespace RepulsiveCoulomb

theorem point_original_plane_finite_surgery_development
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ D : ℂ → ℂ, Continuous D ∧ IsOpenMap D ∧ Function.Bijective D ∧
      ∀ x z,
        (1 / (1 + pointExteriorHalfMass a)) *
            (pointRectifiableConformalEDist a y x z).toReal ≤ dist (D x) (D z) ∧
        dist (D x) (D z) ≤ (pointRectifiableConformalEDist a y x z).toReal := by
  classical
  obtain ⟨c, L, hcdef, hc, hc1, hdis, hregular, hbalance,
      model, chart, hmem, hmodel, hbound⟩ :=
    point_original_plane_finite_surgery_metric_charts ha y
  have hrigid : ∀ i j x, x ∈ (chart i).source ∩ (chart j).source →
      ∃ e : ℂ ≃ᵢ ℂ, (chart i : ℂ → ℂ) =ᶠ[𝓝 x] (fun z ↦ e (chart j z)) := by
    intro i j x hx
    obtain ⟨e, he⟩ := (model i).exists_rigid_overlap (model j) hdis hregular
      x (hbalance x) ((hmodel i).1 hx.1) ((hmodel j).1 hx.2)
    refine ⟨e, ?_⟩
    simpa only [(hmodel i).2, (hmodel j).2] using he
  have hglobal := exists_pointRectifiable_bijective_development_of_actual_atlas
    ha y (⟨c, hc.le⟩ : ℝ≥0) hc
  rw [pointSmoothConformalMetricSpace_topology] at hglobal
  obtain ⟨D, hD, hopen, hbij, hmetric⟩ := hglobal chart hmem hrigid hbound
  refine ⟨D, hD, hopen, hbij, ?_⟩
  intro x z
  have h := hmetric x z
  change c * (pointRectifiableConformalEDist a y x z).toReal ≤ dist (D x) (D z) ∧
    dist (D x) (D z) ≤ (pointRectifiableConformalEDist a y x z).toReal at h
  rwa [hcdef] at h

end RepulsiveCoulomb
