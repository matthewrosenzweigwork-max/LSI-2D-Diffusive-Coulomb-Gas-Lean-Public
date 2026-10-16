module

public import LeanResearch.RepulsiveCoulomb.PointC1DoubleOscillation
public import LeanResearch.RepulsiveCoulomb.PointOscillationTransfer
public import LeanResearch.RepulsiveCoulomb.PointMeasureAverage
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exact product-integral and real-integral forms of the proved C1 inequality,
with the literal nested average used by the downstream manuscript inputs. -/
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem rawPointDoubleOscillation_integrable {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {f : ℂ → ℝ} (hf : Continuous f) (x : ℂ) (R : ℝ) :
    Integrable (fun q : ℂ × ℂ => ‖f q.1-f q.2‖)
      (((rawPointMeasure a y).restrict (ball x R)).prod ((rawPointMeasure a y).restrict (ball x R))) := by
  let ν := (rawPointMeasure a y).restrict (ball x R)
  letI : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact rawPointMeasure_ball_lt_top ha y x R⟩
  have hfi : Integrable f ν := rawPointMeasure_continuous_ball_integrable ha y hf x R
  exact ((hfi.comp_fst ν).sub (hfi.comp_snd ν)).norm

theorem rawPointDoubleAverageOscillation_eq_product {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {f : ℂ → ℝ} (hf : Continuous f) (x : ℂ) (R : ℝ) :
    rawPointDoubleAverageOscillation a y f x R =
      (∫ q : ℂ × ℂ, ‖f q.1-f q.2‖
        ∂((rawPointMeasure a y).restrict (ball x R)).prod ((rawPointMeasure a y).restrict (ball x R))) /
        ((rawPointMeasure a y).real (ball x R))^2 := by
  let ν := (rawPointMeasure a y).restrict (ball x R)
  letI : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact rawPointMeasure_ball_lt_top ha y x R⟩
  have hk : Integrable (fun q : ℂ × ℂ => ‖f q.1-f q.2‖) (ν.prod ν) := rawPointDoubleOscillation_integrable ha y hf x R
  have hp : (∫ q : ℂ × ℂ, ‖f q.1-f q.2‖ ∂ν.prod ν) =
      ∫ u in ball x R, ∫ z in ball x R, ‖f u-f z‖ ∂rawPointMeasure a y ∂rawPointMeasure a y :=
    integral_prod _ hk
  unfold rawPointDoubleAverageOscillation
  simp only [setAverage_eq,smul_eq_mul]
  rw [integral_const_mul,← hp,div_eq_mul_inv,← inv_pow]
  ring

theorem rawPoint_C1_double_oscillation_real {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℂ) {R : ℝ} (hR : 0 < R) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
    let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
    (∫ q : ℂ × ℂ, ‖f q.1-f q.2‖ ∂ν.prod ν) ≤
      (2 * (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q))) *
        ∫ z in ball x (2*R), ‖gradient f z‖ * rawPointWeight a y z := by
  let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball x R)
  let M := (rawPointMeasure (fun j => 2*a j) y).real (ball x R)
  let K := 2 * (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q))
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hk : Integrable (fun q : ℂ × ℂ => ‖f q.1-f q.2‖) (ν.prod ν) :=
    rawPointDoubleOscillation_integrable ha2 y hf.continuous x R
  have hgc : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hgi : IntegrableOn (fun z => ‖gradient f z‖ * rawPointWeight a y z) (ball x (2*R)) :=
    ((hgc.norm.mul (rawPointWeight_continuous ha y)).continuousOn.integrableOn_compact
      (isCompact_closedBall x (2*R))).mono_set ball_subset_closedBall
  have hgn : ∀ z, 0 ≤ ‖gradient f z‖ * rawPointWeight a y z :=
    fun z => mul_nonneg (norm_nonneg _) (rawPointWeight_nonneg a y z)
  have hE0 : 0 ≤ ∫ z in ball x (2*R), ‖gradient f z‖ * rawPointWeight a y z := integral_nonneg hgn
  have hleft : ENNReal.ofReal (∫ q : ℂ × ℂ, ‖f q.1-f q.2‖ ∂ν.prod ν) =
      ∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1-f q.2| ∂ν.prod ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hk (Filter.Eventually.of_forall (fun q => norm_nonneg _))]
    simp only [Real.norm_eq_abs]
  have hright : ENNReal.ofReal (∫ z in ball x (2*R), ‖gradient f z‖ * rawPointWeight a y z) =
      ∫⁻ z in ball x (2*R), ENNReal.ofReal ‖gradient f z‖ * ENNReal.ofReal (rawPointWeight a y z) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hgn)]
    simp only [ENNReal.ofReal_mul (norm_nonneg _)]
  have hb := rawPoint_C1_double_oscillation ha hQ y hf x hR
  change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1-f q.2| ∂ν.prod ν) ≤ _ at hb
  rw [← hleft,← hright] at hb
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 hE0)).mp
  change ENNReal.ofReal (∫ q : ℂ × ℂ, ‖f q.1-f q.2‖ ∂ν.prod ν) ≤ ENNReal.ofReal (K * _)
  rw [ENNReal.ofReal_mul hK0]
  have hcoef : ENNReal.ofReal K = 2 * ENNReal.ofReal (M * Real.sqrt (M * pointGridRelativeIsoperimetricConstant Q)) := by
    dsimp only [K]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hcoef]
  exact hb

end RepulsiveCoulomb
