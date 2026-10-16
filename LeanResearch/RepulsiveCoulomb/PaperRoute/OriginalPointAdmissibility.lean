module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalPointGeometry
public import LeanResearch.RepulsiveCoulomb.PaperRoute.MapBackedLipschitzAdmissibility

@[expose] public section

/-!
# Original-input full locally-Lipschitz weak-(1,2) geometry

This additive extension preserves the C1 endpoint unchanged. It uses the same
original-map data producer, with all constants already fixed from Q, in the
full Lipschitz map-backed DS chain. The output includes the literal physical
path gauge, doubling, global Lipschitz DS, and globally locally-Lipschitz weak
Poincare. The local closed-double-ball theorem uses the original scalar and
its actual physical gradient everywhere in the displayed integrals.

No map, QC, inverse regularity, DS or Poincare certificate is assumed at the
original-input endpoints. No exponent below 2 or whole LSI is asserted.
-/
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- Original data produce one common map for the literal path gauge and full
Lipschitz analytic route. Every displayed coefficient depends only on Q. -/
theorem original_point_locallyLipschitz_geometry
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : (∑ j, a j) ≤ Q) (y : Fin m → ℂ) :
    ∃ F : ℂ ≃ₜ ℂ,
      PositiveFiniteBalls (rawPointMeasure a y) ∧
      GlobalDoublingWith (rawPointMeasure a y) (originalPointDoublingConstant Q) ∧
      GaugeComparable (rawPointMeasure a y) (pullbackMetric F) (originalPointGaugeConstant Q) ∧
      (∀ x z,
        diameterGauge (rawPointMeasure a y) x z / originalPointPathGaugeConstant Q ≤
            (pointRectifiableConformalEDist a y x z).toReal ∧
        (pointRectifiableConformalEDist a y x z).toReal ≤
            originalPointPathGaugeConstant Q * diameterGauge (rawPointMeasure a y) x z) ∧
      PlanarDS.PlanarDSLipschitz (rawPointWeight a y) (originalPointDSConstant Q) ∧
      PlanarDS.WeakOneTwoLipschitz (rawPointMeasure a y) (originalPointWeakTwoConstant Q) 2 ∧
      PlanarDS.WeakOneTwoLocallyLipschitz (rawPointMeasure a y) (originalPointWeakTwoConstant Q) 2 := by
  classical
  have hQn : 0 ≤ Q := (Finset.sum_nonneg fun j _ => ha j).trans hQ
  have hP : 1 ≤ originalPointMassBound Q := by dsimp [originalPointMassBound]; linarith
  obtain ⟨F, hmetricUniform, hLocal, hQC, hcompare, hinverseSet⟩ :=
    original_point_exists_map_data ha hQ y
  let S : Finset ℂ := (pointMap_puncture_image_finite a y F).toFinset
  have hS : (S : Set ℂ) = F '' pointPunctures a y := Set.Finite.coe_toFinset _
  have hinverse : LocallyLipschitzOn ((S : Set ℂ)ᶜ) F.symm := by
    rw [hS]
    exact hinverseSet
  obtain ⟨hμ, hD, hA, hDS, hPI, hPILocal⟩ :=
    mapBacked_planarDS_and_weakOneTwoLocallyLipschitz F hP hP (rawPointWeight_continuous ha y)
      (rawPointWeight_nonneg a y) hLocal hQC hcompare S hinverse
  rw [weightMeasure_rawPointWeight] at hμ hD hA hPI hPILocal
  change GaugeComparable (rawPointMeasure a y) (pullbackMetric F)
    (originalPointGaugeConstant Q) at hA
  have hpath := original_point_pathGauge_of_sameMap hQn y F hmetricUniform hA
  exact ⟨F, hμ, hD, hA, hpath, hDS, hPI, hPILocal⟩

/-- Positive finite balls, quantitative doubling, and the full local-Lipschitz
weak-(1,2) Poincare condition, with constants fixed before configurations. -/
theorem original_point_doubling_and_locallyLipschitz_PI
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : (∑ j, a j) ≤ Q) (y : Fin m → ℂ) :
    PositiveFiniteBalls (rawPointMeasure a y) ∧
    GlobalDoublingWith (rawPointMeasure a y) (originalPointDoublingConstant Q) ∧
    PlanarDS.WeakOneTwoLocallyLipschitz (rawPointMeasure a y) (originalPointWeakTwoConstant Q) 2 := by
  obtain ⟨_, hμ, hD, _, _, _, _, hPI⟩ := original_point_locallyLipschitz_geometry ha hQ y
  exact ⟨hμ, hD, hPI⟩

/-- Strong local physical-gradient interface: Lipschitzness is needed only
on the closed double ball, and both averages use the literal raw measure. -/
theorem original_point_physical_weak_one_two_closedDoubleBall
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : (∑ j, a j) ≤ Q) (y : Fin m → ℂ)
    {v : ℂ → ℝ} {Lv : ℝ≥0} (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hv : LipschitzOnWith Lv v (closedBall z (2 * r))) :
    (⨍ w in ball z r,
      ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      originalPointWeakTwoConstant Q * r * Real.sqrt
        (⨍ w in ball z (2 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y) := by
  obtain ⟨_, _, _, _, _, _, hPI, _⟩ := original_point_locallyLipschitz_geometry ha hQ y
  simpa only [Real.norm_eq_abs, PlanarDS.norm_gradient_eq_norm_fderiv] using
    PlanarDS.weakOneTwo_of_lipschitzOn_closedDoubleBall hPI z hr hv

end RepulsiveCoulomb.PaperRoute
