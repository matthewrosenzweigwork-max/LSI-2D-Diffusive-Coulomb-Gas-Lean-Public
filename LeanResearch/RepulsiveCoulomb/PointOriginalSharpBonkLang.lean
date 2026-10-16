import LeanResearch.RepulsiveCoulomb.PointOriginalSurgeryDevelopment
import LeanResearch.RepulsiveCoulomb.PointMetricMapSharpRescaling
import LeanResearch.RepulsiveCoulomb.PointMetricMapSharpSignedConclusion
import LeanResearch.RepulsiveCoulomb.PointMetricMapLocalSobolev

/-! SOURCE-ONLY, UNCOMPILED. Original-input sharp Bonk--Lang endpoint.
The genuine map is produced by finite angular surgery, actual flat atlas,
covering development and complete pullback length metric. A positive output
sqrt(p) dilation and, if needed, one global conjugation give the actual
orientation-preserving sharp metric/Sobolev/Jacobian conclusion. All constants
use the literal total mass, and the distance ranges over all continuous
Euclidean-rectifiable paths through the established metric identification.
This authored source has not been elaborated or kernel-accepted. -/
noncomputable section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BigOperators
namespace RepulsiveCoulomb

/-- Genuine original-input sharp metric homeomorphism. -/
theorem point_original_plane_sharp_metric_homeomorph
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ F : ℂ ≃ₜ ℂ, ∀ x z,
      (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
          (pointRectifiableConformalEDist a y x z).toReal ≤ ‖F x - F z‖ ∧
      ‖F x - F z‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
          (pointRectifiableConformalEDist a y x z).toReal := by
  obtain ⟨D, hD, hopen, hbij, hmetric⟩ := point_original_plane_finite_surgery_development ha y
  have hmass : pointExteriorHalfMass a = (∑ j, a j) / 2 := by
    unfold pointExteriorHalfMass
    rw [Finset.sum_div]
  have hb : ∀ x z,
      (1 + (∑ j, a j) / 2)⁻¹ * (pointSmoothConformalEDist a y x z).toReal ≤ dist (D x) (D z) ∧
      dist (D x) (D z) ≤ (pointSmoothConformalEDist a y x z).toReal := by
    simpa only [hmass, one_div, pointRectifiableConformalEDist_eq_smooth ha y] using hmetric
  obtain ⟨F, _, hF⟩ := pointAsymmetricMetricMap_exists_sharp_metric_homeomorph_of_supplied_map
    ha y D hD hopen hbij hb
  exact ⟨F, hF⟩

/-- Original coefficients and locations suffice for the sharp conclusion.
The signed Jacobian and outer distortion both have constant p=1+sum(a)/2;
local W12, local W1-infinity, and the actual weak derivative are included.
The infinity clause is derived for the same normalized map from its actual
metric upper bound by the existing proved local Sobolev bridge. -/
theorem point_original_plane_sharp_bonk_lang
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ F : ℂ ≃ₜ ℂ,
      (∀ z, PositiveLocalCircleWindingAt F z) ∧
      (∀ x z,
        (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
            (pointRectifiableConformalEDist a y x z).toReal ≤ ‖F x - F z‖ ∧
        ‖F x - F z‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
            (pointRectifiableConformalEDist a y x z).toReal) ∧
      TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) F (fderiv ℝ F) ∧
      (∀ S : Set ℂ, IsCompact S →
        MemLp F 2 (volume.restrict S) ∧ MemLp (fderiv ℝ F) 2 (volume.restrict S)) ∧
      (∀ S : Set ℂ, IsCompact S →
        MemLp F (⊤ : ℝ≥0∞) (volume.restrict S) ∧
        MemLp (fderiv ℝ F) (⊤ : ℝ≥0∞) (volume.restrict S)) ∧
      (∀ᵐ z ∂volume, HasFDerivAt F (fderiv ℝ F z) z ∧
        0 < (fderiv ℝ F z).toLinearMap.det ∧
        rawPointWeight a y z / (1 + (∑ j, a j) / 2) ≤ (fderiv ℝ F z).toLinearMap.det ∧
        (fderiv ℝ F z).toLinearMap.det ≤ (1 + (∑ j, a j) / 2) * rawPointWeight a y z ∧
        ‖fderiv ℝ F z‖ ^ 2 ≤ (1 + (∑ j, a j) / 2) * (fderiv ℝ F z).toLinearMap.det) := by
  obtain ⟨F, hmetric⟩ := point_original_plane_sharp_metric_homeomorph ha y
  obtain ⟨G, _, _, horient, hGmetric, hweak, hLp, hJac⟩ :=
    pointRectifiableMetricHomeomorph_sharp_analytic_normalization_of_supplied_map ha y F hmetric
  have hupper : ∀ x z, dist (G x) (G z) ≤
      Real.sqrt (1 + (∑ j, a j) / 2) *
        (pointSmoothConformalEDist a y x z).toReal := by
    intro x z
    simpa only [dist_eq_norm, pointRectifiableConformalEDist_eq_smooth ha y x z]
      using (hGmetric x z).2
  have hSobolev := pointMetricMap_localSobolev ha y (Real.sqrt_nonneg _) hupper
  exact ⟨G, horient, hGmetric, hweak, hLp, hSobolev.2.1 ⊤, hJac⟩

end RepulsiveCoulomb
