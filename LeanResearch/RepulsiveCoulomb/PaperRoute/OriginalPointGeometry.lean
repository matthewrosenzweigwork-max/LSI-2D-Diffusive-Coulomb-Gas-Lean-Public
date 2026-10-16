import LeanResearch.RepulsiveCoulomb.PaperRoute.MapBackedDavidSemmes
import LeanResearch.RepulsiveCoulomb.PaperRoute.PointInverseLocalRegularity
import LeanResearch.RepulsiveCoulomb.PointOriginalSharpBonkLang
import LeanResearch.RepulsiveCoulomb.PointMetricMapDifferential

/-!
# Original finite point configurations through the same-map paper route

All quantitative constants are fixed from Q before any finite configuration
or map is selected. The original sharp Bonk--Lang theorem supplies one actual
homeomorphism. Its literal rectifiable metric bounds give both forward local
Lipschitz regularity and inverse local regularity outside its own finite
puncture image. Its actual signed Jacobian supplies the uniform QC and density
comparison premises for the new Semmes/DS chain.

The physical path-gauge comparison uses this very map and the literal
all-rectifiable conformal distance. The output concerns global C1 observables;
full locally-Lipschitz 2-admissibility and the whole LSI are not asserted.
-/

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- Uniform mass/distortion bound, fixed before configurations are chosen. -/
def originalPointMassBound (Q : ℝ) : ℝ := 1 + Q / 2

/-- Uniform literal point-metric bi-Lipschitz constant. -/
def originalPointMetricConstant (Q : ℝ) : ℝ := Real.sqrt (originalPointMassBound Q)

/-- Doubling obtained from the new same-map Semmes chain. -/
def originalPointDoublingConstant (Q : ℝ) : ℝ :=
  mapBackedDoublingConstant (originalPointMassBound Q) (originalPointMassBound Q)

/-- Diameter gauge versus the actual same-map pullback metric. -/
def originalPointGaugeConstant (Q : ℝ) : ℝ :=
  mapBackedGaugeConstant (originalPointMassBound Q) (originalPointMassBound Q)

/-- Diameter gauge versus the literal all-rectifiable weighted path metric. -/
def originalPointPathGaugeConstant (Q : ℝ) : ℝ :=
  originalPointGaugeConstant Q * originalPointMetricConstant Q

/-- New map-backed DS coefficient, independent of the configuration. -/
def originalPointDSConstant (Q : ℝ) : ℝ :=
  mapBackedDSConstant (originalPointMassBound Q) (originalPointMassBound Q)

/-- C1 weak-(1,2) coefficient for exact dilation two. -/
def originalPointWeakTwoConstant (Q : ℝ) : ℝ :=
  2 * originalPointDSConstant Q * Real.sqrt (Real.pi * originalPointDoublingConstant Q)

/-- C1 weak-(1,2) coefficient for exact dilation five. -/
def originalPointWeakFiveConstant (Q : ℝ) : ℝ :=
  originalPointWeakTwoConstant Q * originalPointDoublingConstant Q

/-- Every displayed route constant is positive for every nonnegative mass bound.
This proof fixes no configuration and chooses no map. -/
theorem originalPoint_constants_pos {Q : ℝ} (hQ : 0 ≤ Q) :
    0 < originalPointMassBound Q ∧ 0 < originalPointMetricConstant Q ∧
    0 < originalPointDoublingConstant Q ∧ 0 < originalPointGaugeConstant Q ∧
    0 < originalPointPathGaugeConstant Q ∧ 0 < originalPointDSConstant Q ∧
    0 < originalPointWeakTwoConstant Q ∧ 0 < originalPointWeakFiveConstant Q := by
  have hP : 1 ≤ originalPointMassBound Q := by dsimp [originalPointMassBound]; linarith
  have hPpos : 0 < originalPointMassBound Q := lt_of_lt_of_le zero_lt_one hP
  have hell : 0 < originalPointMetricConstant Q := Real.sqrt_pos.mpr hPpos
  have hH : 0 < semmesQCConstant (originalPointMassBound Q) := by
    unfold semmesQCConstant
    apply sub_pos.mpr
    apply one_lt_pow₀ _ (by norm_num : (4 : ℕ) ≠ 0)
    linarith [Real.exp_pos (9 * Real.pi ^ 2 * originalPointMassBound Q / (4 * Real.log 2))]
  have hT : 0 < weakQSTwoScale (semmesQCConstant (originalPointMassBound Q)) := by
    unfold weakQSTwoScale
    positivity
  have hD : 0 < originalPointDoublingConstant Q := by
    unfold originalPointDoublingConstant mapBackedDoublingConstant semmesDoublingConstant
    positivity
  have hA : 0 < originalPointGaugeConstant Q := by
    unfold originalPointGaugeConstant mapBackedGaugeConstant semmesGaugeConstant
    positivity
  have hB : 0 < originalPointPathGaugeConstant Q := mul_pos hA hell
  have hL : 0 < originalPointDSConstant Q := mapBackedDSConstant_pos hP hP
  have hW2 : 0 < originalPointWeakTwoConstant Q := by
    unfold originalPointWeakTwoConstant
    positivity
  exact ⟨hPpos, hell, hD, hA, hB, hL, hW2, mul_pos hW2 hD⟩

/-- The raw measure is literally the measure used by the new chain. -/
theorem weightMeasure_rawPointWeight {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    weightMeasure (rawPointWeight a y) = rawPointMeasure a y := rfl

/-- Original coefficients and locations produce one map with actual uniform
analytic data and the actual inverse regularity off its own puncture image.
This reusable helper accepts no supplied map or analytic certificate. -/
theorem original_point_exists_map_data
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : (∑ j, a j) ≤ Q) (y : Fin m → ℂ) :
    ∃ F : ℂ ≃ₜ ℂ,
      (∀ x z,
        (pointRectifiableConformalEDist a y x z).toReal ≤
            originalPointMetricConstant Q * ‖F x - F z‖ ∧
        ‖F x - F z‖ ≤ originalPointMetricConstant Q *
            (pointRectifiableConformalEDist a y x z).toReal) ∧
      (∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R)) ∧
      (∀ᵐ z ∂volume,
        HasFDerivAt F (fderiv ℝ F z) z ∧ 0 < signedJacobian F z ∧
          ‖fderiv ℝ F z‖ ^ 2 ≤ originalPointMassBound Q * signedJacobian F z) ∧
      (∀ᵐ z ∂volume,
        (originalPointMassBound Q)⁻¹ * rawPointWeight a y z ≤ signedJacobian F z ∧
          signedJacobian F z ≤ originalPointMassBound Q * rawPointWeight a y z) ∧
      LocallyLipschitzOn (F '' pointPunctures a y)ᶜ F.symm := by
  classical
  have hmass : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  have hQn : 0 ≤ Q := hmass.trans hQ
  let p : ℝ := 1 + (∑ j, a j) / 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hP : 1 ≤ originalPointMassBound Q := by dsimp [originalPointMassBound]; linarith
  have hpP : p ≤ originalPointMassBound Q := by dsimp [p, originalPointMassBound]; linarith
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hsqrtP : Real.sqrt p ≤ originalPointMetricConstant Q := Real.sqrt_le_sqrt hpP
  have hell : 0 < originalPointMetricConstant Q :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hP)
  obtain ⟨F, _hOrientation, hMetric, _hWeak, _hL2, _hLinf, hActual⟩ :=
    point_original_plane_sharp_bonk_lang ha y
  have hmetricUniform : ∀ x z,
      (pointRectifiableConformalEDist a y x z).toReal ≤
          originalPointMetricConstant Q * ‖F x - F z‖ ∧
      ‖F x - F z‖ ≤ originalPointMetricConstant Q *
          (pointRectifiableConformalEDist a y x z).toReal := by
    intro x z
    have hm := hMetric x z
    change (Real.sqrt p)⁻¹ * _ ≤ _ ∧ _ ≤ Real.sqrt p * _ at hm
    refine ⟨?_, hm.2.trans (mul_le_mul_of_nonneg_right hsqrtP ENNReal.toReal_nonneg)⟩
    have hmul := mul_le_mul_of_nonneg_left hm.1 hsqrt.le
    have hlow : (pointRectifiableConformalEDist a y x z).toReal ≤
        Real.sqrt p * ‖F x - F z‖ := by
      simpa only [← mul_assoc, mul_inv_cancel₀ hsqrt.ne', one_mul] using hmul
    exact hlow.trans (mul_le_mul_of_nonneg_right hsqrtP (norm_nonneg _))
  have hupper : ∀ x z, dist (F x) (F z) ≤ originalPointMetricConstant Q *
      (pointSmoothConformalEDist a y x z).toReal := by
    intro x z
    simpa only [dist_eq_norm, pointRectifiableConformalEDist_eq_smooth ha y x z]
      using (hmetricUniform x z).2
  have hlower : ∀ x z, (pointSmoothConformalEDist a y x z).toReal ≤
      originalPointMetricConstant Q * dist (F x) (F z) := by
    intro x z
    simpa only [dist_eq_norm, pointRectifiableConformalEDist_eq_smooth ha y x z]
      using (hmetricUniform x z).1
  have hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R) := by
    intro R
    exact ⟨_, pointMetricMap_lipschitzOn_ball ha y hell.le hupper R⟩
  have hQC : ∀ᵐ z ∂volume,
      HasFDerivAt F (fderiv ℝ F z) z ∧ 0 < signedJacobian F z ∧
        ‖fderiv ℝ F z‖ ^ 2 ≤ originalPointMassBound Q * signedJacobian F z := by
    filter_upwards [hActual] with z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    exact hz.2.2.2.2.trans (mul_le_mul_of_nonneg_right hpP hz.2.1.le)
  have hcompare : ∀ᵐ z ∂volume,
      (originalPointMassBound Q)⁻¹ * rawPointWeight a y z ≤ signedJacobian F z ∧
        signedJacobian F z ≤ originalPointMassBound Q * rawPointWeight a y z := by
    filter_upwards [hActual] with z hz
    have hw : 0 ≤ rawPointWeight a y z := rawPointWeight_nonneg a y z
    refine ⟨?_, hz.2.2.2.1.trans (mul_le_mul_of_nonneg_right hpP hw)⟩
    calc
      (originalPointMassBound Q)⁻¹ * rawPointWeight a y z =
          rawPointWeight a y z / originalPointMassBound Q := by ring
      _ ≤ rawPointWeight a y z / p := div_le_div_of_nonneg_left hw hp hpP
      _ ≤ signedJacobian F z := hz.2.2.1
  exact ⟨F, hmetricUniform, hLocal, hQC, hcompare,
    pointMapInverse_locallyLipschitzOn_of_metric_lower ha y F hell.le hlower⟩

/-- The same original metric map turns its Semmes diameter gauge into a
comparison with the literal all-rectifiable conformal path distance. -/
theorem original_point_pathGauge_of_sameMap
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (hQ : 0 ≤ Q) (y : Fin m → ℂ)
    (F : ℂ ≃ₜ ℂ)
    (hmetricUniform : ∀ x z,
      (pointRectifiableConformalEDist a y x z).toReal ≤
          originalPointMetricConstant Q * ‖F x - F z‖ ∧
      ‖F x - F z‖ ≤ originalPointMetricConstant Q *
          (pointRectifiableConformalEDist a y x z).toReal)
    (hA : GaugeComparable (rawPointMeasure a y) (pullbackMetric F) (originalPointGaugeConstant Q)) :
    ∀ x z,
      diameterGauge (rawPointMeasure a y) x z / originalPointPathGaugeConstant Q ≤
          (pointRectifiableConformalEDist a y x z).toReal ∧
      (pointRectifiableConformalEDist a y x z).toReal ≤
          originalPointPathGaugeConstant Q * diameterGauge (rawPointMeasure a y) x z := by
  have hell : 0 < originalPointMetricConstant Q := (originalPoint_constants_pos hQ).2.1
  intro x z
  have hg : diameterGauge (rawPointMeasure a y) x z / originalPointGaugeConstant Q ≤
      ‖F x - F z‖ ∧ ‖F x - F z‖ ≤
        originalPointGaugeConstant Q * diameterGauge (rawPointMeasure a y) x z := by
    simpa only [pullbackMetric_dist] using hA.2 x z
  refine ⟨?_, ?_⟩
  · rw [originalPointPathGaugeConstant, ← div_div]
    apply (div_le_iff₀ hell).mpr
    simpa only [mul_comm] using hg.1.trans (hmetricUniform x z).2
  · calc
      (pointRectifiableConformalEDist a y x z).toReal ≤
          originalPointMetricConstant Q * ‖F x - F z‖ := (hmetricUniform x z).1
      _ ≤ originalPointMetricConstant Q *
          (originalPointGaugeConstant Q * diameterGauge (rawPointMeasure a y) x z) :=
        mul_le_mul_of_nonneg_left hg.2 hell.le
      _ = originalPointPathGaugeConstant Q * diameterGauge (rawPointMeasure a y) x z := by
        unfold originalPointPathGaugeConstant
        ring

/-- The original data alone produce the same-map gauge, literal path
comparison, planar DS, and both C1 weak-Poincare dilations. No supplied map or
analytic conclusion is a premise. -/
theorem original_point_localGeometry
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
      PlanarDS.PlanarDSC1 (rawPointWeight a y) (originalPointDSConstant Q) ∧
      PlanarDS.WeakOneTwoC1 (rawPointMeasure a y) (originalPointWeakTwoConstant Q) 2 ∧
      PlanarDS.WeakOneTwoC1 (rawPointMeasure a y) (originalPointWeakFiveConstant Q) 5 := by
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
  obtain ⟨hμ, hD, hA, hDS, hPI2, hPI5⟩ :=
    mapBacked_planarDS_and_weakOneTwoC1 F hP hP (rawPointWeight_continuous ha y)
      (rawPointWeight_nonneg a y) hLocal hQC hcompare S hinverse
  rw [weightMeasure_rawPointWeight] at hμ hD hA hPI2 hPI5
  change GaugeComparable (rawPointMeasure a y) (pullbackMetric F)
    (originalPointGaugeConstant Q) at hA
  have hpath := original_point_pathGauge_of_sameMap hQn y F hmetricUniform hA
  exact ⟨F, hμ, hD, hA, hpath, hDS, hPI2, hPI5⟩

/-- The exact existing physical-gradient C1 consumer shape is obtained from
this new route, with the identical raw measure and no old DS/PI producer. -/
theorem original_point_physical_weak_one_two
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : (∑ j, a j) ≤ Q) (y : Fin m → ℂ)
    (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (⨍ w in ball z r,
      ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      originalPointWeakFiveConstant Q * r * Real.sqrt
        (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y) := by
  obtain ⟨F, hμ, hD, hA, hpath, hDS, hPI2, hPI5⟩ := original_point_localGeometry ha hQ y
  simpa only [Real.norm_eq_abs, PlanarDS.norm_gradient_eq_norm_fderiv] using hPI5 v hv z r hr

end RepulsiveCoulomb.PaperRoute
