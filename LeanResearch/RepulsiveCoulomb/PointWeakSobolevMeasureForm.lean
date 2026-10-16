import LeanResearch.RepulsiveCoulomb.PointWeakSobolevNormalized

/-! The actual weak estimate in the two-measure form consumed by smooth
truncation, with explicit normalization and no assumed moment identities. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointWeakSobolevBallFactor {m : ℕ} (Q P : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) (R : ℝ) : ℝ :=
  pointWeakSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
    (rawPointMeasure a y).real (ball c R) / ((rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q

theorem pointWeakSobolevBallFactor_nonneg {m : ℕ} (Q : ℝ) {P : ℝ} (hP : 0 < P)
    (a : Fin m → ℝ) (y : Fin m → ℂ) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ pointWeakSobolevBallFactor Q P a y c R := by
  unfold pointWeakSobolevBallFactor
  exact div_nonneg (mul_nonneg (mul_nonneg (pointWeakSobolevConstant_pos Q hP).le
    (Real.rpow_nonneg hR _)) ENNReal.toReal_nonneg) (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem pointWeakSobolevBallFactor_mul_energy {m : ℕ} (Q P : ℝ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) (c : ℂ) (R : ℝ) {I : ℝ} (hI : 0 ≤ I) :
    pointWeakSobolevBallFactor Q P a y c R * I ^ pointSobolevKappa Q =
      pointWeakSobolevConstant Q P * R ^ (2 * pointSobolevKappa Q) *
        (rawPointMeasure a y).real (ball c R) *
        (I / (rawPointMeasure a y).real (ball c R)) ^ pointSobolevKappa Q := by
  unfold pointWeakSobolevBallFactor
  rw [Real.div_rpow hI (show 0 ≤ (rawPointMeasure a y).real (ball c R) from ENNReal.toReal_nonneg)]
  ring

theorem rawPointMeasure_weak_sobolev_measure_form {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r, ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y))
    (c : ℂ) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    ENNReal.ofReal (t ^ (2 * pointSobolevKappa Q)) *
      ((rawPointMeasure a y).restrict (ball c R))
        {x | t < ‖v x - (⨍ z in ball c R, v z ∂rawPointMeasure a y)‖} ≤
      ENNReal.ofReal (pointWeakSobolevBallFactor Q P a y c R) *
        (∫⁻ x in ball c (11 * R), ENNReal.ofReal (‖gradient v x‖ ^ 2) ∂rawPointMeasure a y) ^ pointSobolevKappa Q := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  have hκ : 0 ≤ pointSobolevKappa Q := (lt_trans zero_lt_one (pointSobolevKappa_gt_one hQ0)).le
  have hg : Continuous (fun z => ‖gradient v z‖ ^ 2) := by
    simp_rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hv.continuous_fderiv one_ne_zero).norm.pow 2
  have hi := ofReal_integral_eq_lintegral_ofReal
    (rawPointMeasure_continuous_ball_integrable ha y hg c (11 * R))
    (Eventually.of_forall (fun z => sq_nonneg ‖gradient v z‖))
  rw [← hi, ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ ∫ x in ball c (11 * R), ‖gradient v x‖ ^ 2 ∂rawPointMeasure a y from integral_nonneg (fun z => sq_nonneg _)) hκ,
    ← ENNReal.ofReal_mul (pointWeakSobolevBallFactor_nonneg Q hP a y c hR.le),
    pointWeakSobolevBallFactor_mul_energy Q P a y c R (integral_nonneg (fun z => sq_nonneg _))]
  have hs : MeasurableSet {x | t < ‖v x - (⨍ z in ball c R, v z ∂rawPointMeasure a y)‖} :=
    measurableSet_lt measurable_const (hv.continuous.sub continuous_const).norm.measurable
  rw [Measure.restrict_apply hs]
  have he : {x | t < ‖v x - (⨍ z in ball c R, v z ∂rawPointMeasure a y)‖} ∩ ball c R =
      {x | x ∈ ball c R ∧ t < ‖v x - (⨍ z in ball c R, v z ∂rawPointMeasure a y)‖} := by ext x; simp [and_comm]
  rw [he]
  exact rawPointMeasure_weak_sobolev_normalized ha hQ hP y v _ hv.continuous hg (fun z => sq_nonneg _) hPI c hR ht

end RepulsiveCoulomb
