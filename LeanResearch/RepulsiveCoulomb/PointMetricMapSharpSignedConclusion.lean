module

public import LeanResearch.RepulsiveCoulomb.PlanarHomeomorphCircleOrientation
public import LeanResearch.RepulsiveCoulomb.PointMetricMapSharpDistortion
public import LeanResearch.RepulsiveCoulomb.PointMetricMapLocalSobolev
public import LeanResearch.RepulsiveCoulomb.PointRectifiableConformalMetric

@[expose] public section

/-!
# Sharp signed analytic conclusion for a supplied actual metric homeomorphism

Source-only candidate, not compiled or accepted. The orientation premise is
constructed by `pointMetricHomeomorph_exists_positive_circle_normalization`:
one global output conjugation, if necessary, suffices. The lower/upper
Jacobian constants and outer distortion are all `L²`, not the older `L⁴`.

The final theorem uses the literal all-continuous-rectifiable-curve distance,
sets `q = ∑ j, a j` in its own statement, and gives the accepted weak derivative
plus actual local L² membership. Its input still includes an actual global
metric homeomorphism with the sharp metric bounds. No unconditional
Bonk--Lang map-existence theorem is asserted.
-/

noncomputable section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BigOperators
namespace RepulsiveCoulomb

/-- Combine genuine positivity with the sharp absolute determinant estimate.
Only the positivity clause of the older signed theorem is used; its `L⁴`
outer-distortion bound is discarded. -/
theorem pointMetricHomeomorph_ae_sharp_signed_jacobian_bounds
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal)
    (horient : ∀ z, z ∉ pointPunctures a y → PositiveLocalCircleWindingAt F z) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z ∧
      0 < (fderiv ℝ F z).toLinearMap.det ∧
      rawPointWeight a y z / L ^ 2 ≤ (fderiv ℝ F z).toLinearMap.det ∧
      (fderiv ℝ F z).toLinearMap.det ≤ L ^ 2 * rawPointWeight a y z ∧
      ‖fderiv ℝ F z‖ ^ 2 ≤ L ^ 2 * (fderiv ℝ F z).toLinearMap.det := by
  filter_upwards [pointMetricHomeomorph_ae_signed_jacobian_bounds ha y F hL hmetric horient,
    pointMetricHomeomorph_ae_sharp_jacobian_bounds ha y F hL hmetric] with z hpos hsharp
  refine ⟨hsharp.1, hpos.2.1, ?_⟩
  simpa only [abs_of_pos hpos.2.1] using hsharp.2

/-- Fully derived orientation normalization, weak derivatives, and sharp
signed estimates for an already supplied actual metric homeomorphism. -/
theorem pointMetricHomeomorph_exists_sharp_signed_normalization
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 1 ≤ L)
    (hmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∃ G : ℂ ≃ₜ ℂ, (G = F ∨ G = planarOutputConjugate F) ∧
      (∀ p z, ‖G p - G z‖ = ‖F p - F z‖) ∧
      (∀ z, PositiveLocalCircleWindingAt G z) ∧
      (∀ p z,
        L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖G p - G z‖ ∧
        ‖G p - G z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal) ∧
      TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) G (fderiv ℝ G) ∧
      (∀ S : Set ℂ, IsCompact S →
        MemLp G 2 (volume.restrict S) ∧ MemLp (fderiv ℝ G) 2 (volume.restrict S)) ∧
      (∀ᵐ z ∂volume, HasFDerivAt G (fderiv ℝ G z) z ∧
        0 < (fderiv ℝ G z).toLinearMap.det ∧
        rawPointWeight a y z / L ^ 2 ≤ (fderiv ℝ G z).toLinearMap.det ∧
        (fderiv ℝ G z).toLinearMap.det ≤ L ^ 2 * rawPointWeight a y z ∧
        ‖fderiv ℝ G z‖ ^ 2 ≤ L ^ 2 * (fderiv ℝ G z).toLinearMap.det) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨G, hchoice, hnorm, horient⟩ :=
    pointMetricHomeomorph_exists_positive_circle_normalization ha y F hLp hmetric
  have hGmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖G p - G z‖ ∧
      ‖G p - G z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal := by
    intro p z
    simpa only [hnorm p z] using hmetric p z
  have hupper : ∀ p z, dist (G p) (G z) ≤ L * (pointSmoothConformalEDist a y p z).toReal := by
    intro p z
    simpa only [dist_eq_norm] using (hGmetric p z).2
  have hW := pointMetricMap_localW12 ha y hLp.le hupper
  refine ⟨G, hchoice, hnorm, horient, hGmetric, hW.1, hW.2.1, ?_⟩
  filter_upwards [pointMetricHomeomorph_ae_sharp_signed_jacobian_bounds
    ha y G hL hGmetric (fun z _ => horient z)] with z hz
  exact ⟨hz.1.hasFDerivAt, hz.2⟩

/-- The literal manuscript-level analytic conclusion, conditional solely on
a supplied actual global sharp metric homeomorphism. Total mass is literally
`∑ j, a j`; both the weight-comparison and outer-distortion constant are
`1 + (∑ j, a j) / 2`. The metric is the infimum over every continuous
Euclidean-rectifiable path, identified by the existing proved theorem. -/
theorem pointRectifiableMetricHomeomorph_sharp_analytic_normalization_of_supplied_map
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (F : ℂ ≃ₜ ℂ)
    (hmetric : ∀ p z,
      (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
          (pointRectifiableConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
          (pointRectifiableConformalEDist a y p z).toReal) :
    ∃ G : ℂ ≃ₜ ℂ, (G = F ∨ G = planarOutputConjugate F) ∧
      (∀ p z, ‖G p - G z‖ = ‖F p - F z‖) ∧
      (∀ z, PositiveLocalCircleWindingAt G z) ∧
      (∀ p z,
        (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
            (pointRectifiableConformalEDist a y p z).toReal ≤ ‖G p - G z‖ ∧
        ‖G p - G z‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
            (pointRectifiableConformalEDist a y p z).toReal) ∧
      TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) G (fderiv ℝ G) ∧
      (∀ S : Set ℂ, IsCompact S →
        MemLp G 2 (volume.restrict S) ∧ MemLp (fderiv ℝ G) 2 (volume.restrict S)) ∧
      (∀ᵐ z ∂volume, HasFDerivAt G (fderiv ℝ G z) z ∧
        0 < (fderiv ℝ G z).toLinearMap.det ∧
        rawPointWeight a y z / (1 + (∑ j, a j) / 2) ≤ (fderiv ℝ G z).toLinearMap.det ∧
        (fderiv ℝ G z).toLinearMap.det ≤ (1 + (∑ j, a j) / 2) * rawPointWeight a y z ∧
        ‖fderiv ℝ G z‖ ^ 2 ≤ (1 + (∑ j, a j) / 2) * (fderiv ℝ G z).toLinearMap.det) := by
  have hq : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  have hc : 0 ≤ 1 + (∑ j, a j) / 2 := by positivity
  have hL : 1 ≤ Real.sqrt (1 + (∑ j, a j) / 2) := by
    rw [Real.le_sqrt (by norm_num) hc]
    nlinarith
  have hmetric' : ∀ p z,
      (Real.sqrt (1 + (∑ j, a j) / 2))⁻¹ *
          (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ Real.sqrt (1 + (∑ j, a j) / 2) *
          (pointSmoothConformalEDist a y p z).toReal := by
    intro p z
    simpa only [pointRectifiableConformalEDist_eq_smooth ha y p z] using hmetric p z
  have hL2 := Real.sq_sqrt hc
  obtain ⟨G, hchoice, hnorm, horient, hGmetric, hweak, hLp, hJ⟩ :=
    pointMetricHomeomorph_exists_sharp_signed_normalization ha y F hL hmetric'
  refine ⟨G, hchoice, hnorm, horient, ?_, hweak, hLp, ?_⟩
  · intro p z
    simpa only [pointRectifiableConformalEDist_eq_smooth ha y p z] using hGmetric p z
  · simpa only [hL2] using hJ

end RepulsiveCoulomb
