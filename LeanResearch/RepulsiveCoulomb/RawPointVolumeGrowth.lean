import LeanResearch.RepulsiveCoulomb.RawPointWeightGeometry
import Mathlib.MeasureTheory.Measure.Doubling

/-! Quantitative volume growth for the raw product measure, with constants
chosen before the configuration. This is the volume condition used later in
the local Sobolev step; it does not by itself give a Poincare inequality. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointGrowthConstant (Q : ℝ) : ℝ :=
  4 * Real.pi * (2 : ℝ) ^ Q / pointLowerConstant 1 Q

theorem rawPointGrowthConstant_pos (Q : ℝ) : 0 < rawPointGrowthConstant Q := by
  unfold rawPointGrowthConstant
  exact div_pos (by positivity) (pointLowerConstant_pos 1 Q)

theorem rawPointWeight_volume_growth {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 1 ≤ s) :
    (∫ z in closedBall c (s * r), rawPointWeight a y z) ≤
      rawPointGrowthConstant Q * s ^ (Q + 2) *
        ∫ z in closedBall c r, rawPointWeight a y z := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hf := rawPointBallFactor_dilate ha hQ y c (r := r / 2) (s := 2 * s)
    (by positivity) (by linarith)
  have he : (2 * s) * (r / 2) = s * r := by ring
  rw [he] at hf
  have hl := rawPointWeight_ball_integral_lower ha hQ y c (r := r / 2) (by positivity)
  have he2 : 2 * (r / 2) = r := by ring
  rw [he2] at hl
  calc
    _ ≤ Real.pi * (s * r) ^ 2 * rawPointBallFactor a y c (s * r) :=
      rawPointWeight_ball_integral_upper ha y c (by positivity)
    _ ≤ Real.pi * (s * r) ^ 2 * ((2 * s) ^ Q * rawPointBallFactor a y c (r / 2)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (rawPointGrowthConstant Q * s ^ (Q + 2)) *
        (pointLowerConstant 1 Q * (r / 2) ^ 2 * rawPointBallFactor a y c (r / 2)) := by
      unfold rawPointGrowthConstant
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs0.le,
        Real.rpow_add hs0, Real.rpow_two]
      field_simp [ne_of_gt (pointLowerConstant_pos 1 Q)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg (rawPointGrowthConstant_pos Q).le (Real.rpow_nonneg hs0.le _))

theorem rawPointMeasure_volume_growth {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 1 ≤ s) :
    rawPointMeasure a y (closedBall c (s * r)) ≤
      ENNReal.ofReal (rawPointGrowthConstant Q * s ^ (Q + 2)) *
        rawPointMeasure a y (closedBall c r) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [rawPointMeasure_closedBall ha y c (s * r), rawPointMeasure_closedBall ha y c r,
    ← ENNReal.ofReal_mul (mul_nonneg (rawPointGrowthConstant_pos Q).le (Real.rpow_nonneg hs0.le _))]
  exact ENNReal.ofReal_le_ofReal (rawPointWeight_volume_growth ha hQ y c hr hs)

theorem rawPointWeight_nested_volume_growth {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c d : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hsub : closedBall c r ⊆ closedBall d R) :
    (∫ z in closedBall d R, rawPointWeight a y z) ≤
      rawPointGrowthConstant Q * (2 * R / r) ^ (Q + 2) *
        ∫ z in closedBall c r, rawPointWeight a y z := by
  have hcd : dist c d ≤ R := mem_closedBall.mp (hsub (mem_closedBall_self hr.le))
  have hb : closedBall d R ⊆ closedBall c (2 * R) := by
    intro z hz
    have hzR := mem_closedBall.mp hz
    have ht := dist_triangle z d c
    have hdc : dist d c ≤ R := by simpa only [dist_comm] using hcd
    exact mem_closedBall.mpr (by linarith)
  have hm := setIntegral_mono_set (rawPointWeight_ball_integrable ha y c (2 * R))
    (Eventually.of_forall (rawPointWeight_nonneg a y)) (Eventually.of_forall hb)
  have hs : 1 ≤ 2 * R / r := (le_div_iff₀ hr).mpr (by linarith)
  have hg := rawPointWeight_volume_growth ha hQ y c hr hs
  have he : (2 * R / r) * r = 2 * R := div_mul_cancel₀ _ hr.ne'
  rw [he] at hg
  exact hm.trans hg

/-- Equivalent lower growth estimate, with all denominators proved positive. -/
theorem rawPointWeight_nested_volume_lower {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c d : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hsub : closedBall c r ⊆ closedBall d R) :
    (∫ z in closedBall d R, rawPointWeight a y z) /
      (rawPointGrowthConstant Q * (2 * R / r) ^ (Q + 2)) ≤
        ∫ z in closedBall c r, rawPointWeight a y z := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hd : 0 < rawPointGrowthConstant Q * (2 * R / r) ^ (Q + 2) :=
    mul_pos (rawPointGrowthConstant_pos Q) (Real.rpow_pos_of_pos (by positivity) _)
  apply (div_le_iff₀ hd).mpr
  simpa only [mul_comm] using rawPointWeight_nested_volume_growth ha hQ y c d hr hrR hsub

theorem rawPointMeasure_sphere {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) (r : ℝ) : rawPointMeasure a y (sphere c r) = 0 :=
  withDensity_absolutelyContinuous volume _ (Measure.addHaar_sphere volume c r)

theorem rawPointMeasure_closedBall_eq_ball {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℂ) (r : ℝ) : rawPointMeasure a y (closedBall c r) = rawPointMeasure a y (ball c r) := by
  apply measure_congr
  have hn : ∀ᵐ z ∂rawPointMeasure a y, z ∉ sphere c r := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using rawPointMeasure_sphere a y c r
  filter_upwards [hn] with z hz
  simp only [mem_closedBall, mem_ball, mem_sphere] at *
  exact propext ⟨fun h ↦ lt_of_le_of_ne h hz, le_of_lt⟩

theorem rawPointMeasure_ball_doubling {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    rawPointMeasure a y (ball c (2 * r)) ≤
      ENNReal.ofReal (rawPointDoublingConstant Q) * rawPointMeasure a y (ball c r) := by
  simpa only [rawPointMeasure_closedBall_eq_ball] using rawPointMeasure_doubling ha hQ y c hr

theorem rawPointMeasure_uniformlyLocallyDoubling {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    IsUnifLocDoublingMeasure (rawPointMeasure a y) := by
  let C : NNReal := ⟨rawPointDoublingConstant Q, (rawPointDoublingConstant_pos Q).le⟩
  refine ⟨⟨C, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  intro c
  have he : (C : ℝ≥0∞) = ENNReal.ofReal (rawPointDoublingConstant Q) := ENNReal.ofReal_coe_nnreal.symm
  rw [he]
  exact rawPointMeasure_doubling ha hQ y c hr

theorem rawPointMeasure_closedBall_lt_top {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) (r : ℝ) :
    rawPointMeasure a y (closedBall c r) < ⊤ := by
  rw [rawPointMeasure_closedBall ha y c r]
  exact ENNReal.ofReal_lt_top

theorem rawPointMeasure_ball_pos {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < rawPointMeasure a y (ball c r) := by
  have hl := rawPointWeight_ball_integral_lower ha (le_refl (∑ j, a j)) y c (r := r / 2) (by positivity)
  have he : 2 * (r / 2) = r := by ring
  rw [he] at hl
  have hf : 0 < rawPointBallFactor a y c (r / 2) :=
    Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (by positivity) _
  have hp : 0 < pointLowerConstant 1 (∑ j, a j) * (r / 2) ^ 2 * rawPointBallFactor a y c (r / 2) :=
    mul_pos (mul_pos (pointLowerConstant_pos 1 _) (by positivity)) hf
  rw [← rawPointMeasure_closedBall_eq_ball a y c r, rawPointMeasure_closedBall ha y c r]
  exact ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hp hl)

end RepulsiveCoulomb
