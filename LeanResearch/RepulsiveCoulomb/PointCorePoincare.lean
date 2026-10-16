import LeanResearch.RepulsiveCoulomb.PointMomentTail
import LeanResearch.RepulsiveCoulomb.PointUniformLocalGeometry
import Mathlib.Probability.Moments.Variance

/-! Uniform global Poincare on the actual original core, using the full-domain
moment bound for subtraction of a noncompact constant. -/
noncomputable section
open Set MeasureTheory Metric Filter ProbabilityTheory
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointCore_uniform_poincare {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ P : ℝ, 0 < P ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
    variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
      P * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
  obtain ⟨C, hC, hU⟩ := pointForm_weighted_moment_bound (Q := Q) hγ
  let R : ℝ := 1 + Real.sqrt (2 * C)
  have hR : 1 ≤ R := by dsimp only [R]; linarith [Real.sqrt_nonneg (2 * C)]
  have hRp : 0 < R := by linarith
  have hR2 : 2 * C ≤ R ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * C by positivity)
    dsimp only [R]
    nlinarith [Real.sqrt_nonneg (2 * C)]
  let K : ℝ := pointGaussianSobolevFactor Q (pointUniformMeanTransferConstant Q) *
    Real.exp (61 * γ * R ^ 2) * R ^ 2
  have hK : 0 < K := mul_pos
    (mul_pos (pointGaussianSobolevFactor_pos Q (pointUniformMeanTransferConstant_pos Q)) (Real.exp_pos _))
    (sq_pos_of_pos hRp)
  refine ⟨2 * K + 1, by positivity, ?_⟩
  intro m a ha y hQ φ
  let _ := pointMeasure_isProbability hγ ha y
  let c : ℝ := ⨍ z in ball (0 : ℂ) R, φ z ∂pointMeasure γ a y
  let g : ℂ → ℝ := fun x => φ x - c
  let u := pointFormSubtractConstant hγ ha y (pointFormCore hγ ha y φ) c
  have hvalue := pointCore_subtractConstant_value hγ ha y φ c
  have hmeq : (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) =ᵐ[pointMeasure γ a y]
      (fun x => ‖x‖ ^ 2 * g x ^ 2) := by
    filter_upwards [hvalue] with x hx
    change ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 = ‖x‖ ^ 2 * (φ x - c) ^ 2
    rw [hx]
  obtain ⟨hmi, hmb⟩ := hU m a ha y hQ u
  have hm : Integrable (fun x : ℂ => ‖x‖ ^ 2 * g x ^ 2) (pointMeasure γ a y) := hmi.congr hmeq
  have hmBound : (∫ x, ‖x‖ ^ 2 * g x ^ 2 ∂pointMeasure γ a y) ≤ C *
      ((∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (∫ x, g x ^ 2 ∂pointMeasure γ a y)) := by
    rw [integral_congr_ae hmeq] at hmb
    simpa only [u, pointCore_subtractConstant_norm_sq, g] using hmb
  have hg : Integrable (fun x : ℂ => g x ^ 2) (pointMeasure γ a y) :=
    pointCore_subtractConstant_square_integrable hγ ha y φ c
  have hE := testFunction_physical_energy_integrable (pointDomain a y) φ (pointMeasure γ a y)
  have hl0 : (∫ x in ball (0 : ℂ) R, g x ^ 2 ∂pointMeasure γ a y) ≤
      K * (∫ x in ball (0 : ℂ) (11 * R), ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) := by
    simpa only [g, c, K, Real.norm_eq_abs, sq_abs] using
      (pointGaussian_uniform_local_geometry hγ ha hQ y (φ : ℂ → ℝ)
        (φ.contDiff.of_le (by simp)) hR).2
  have hgradle : (∫ x in ball (0 : ℂ) (11 * R), ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ≤
      ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y :=
    setIntegral_le_integral hE (Eventually.of_forall (fun x => sq_nonneg _))
  have hl := hl0.trans (mul_le_mul_of_nonneg_left hgradle hK.le)
  have ht := (planar_quadratic_moment_tail hRp g hg hm).trans hmBound
  have hmass : (∫ x, g x ^ 2 ∂pointMeasure γ a y) ≤
      (2 * K + 1) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) :=
    quadratic_tail_absorb hC hR2 (integral_nonneg (fun x => sq_nonneg _))
      (integral_add_compl measurableSet_ball hg) hl ht
  have hga : AEStronglyMeasurable g (pointMeasure γ a y) :=
    (φ.continuous.sub continuous_const).aestronglyMeasurable
  have hv : variance g (pointMeasure γ a y) = variance (φ : ℂ → ℝ) (pointMeasure γ a y) :=
    variance_sub_const φ.continuous.aestronglyMeasurable c
  rw [← hv]
  exact (variance_le_expectation_sq hga).trans hmass

end RepulsiveCoulomb
