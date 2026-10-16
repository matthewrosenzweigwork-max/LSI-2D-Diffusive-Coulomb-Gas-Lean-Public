import LeanResearch.RepulsiveCoulomb.RawPointMeasureMapScaling
import LeanResearch.RepulsiveCoulomb.DoubleLayerCake

/-! Exact scaling of the physical double-oscillation product measure. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem rawPoint_double_oscillation_scaling {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {h : ℝ} (hh : 0 < h)
    (f : ℂ → ℝ) (hf : Measurable f) (c : ℂ) (R : ℝ) :
    let ν := (rawPointMeasure (fun j => 2*a j) y).restrict (ball c R)
    let ν' := (rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).restrict (ball (h⁻¹ • c) (R/h))
    (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f (h⁻¹ • q.1) - f (h⁻¹ • q.2)| ∂ν.prod ν) =
      ENNReal.ofReal (rawPointLengthScale a h ^ 4) *
        ∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f q.1 - f q.2| ∂ν'.prod ν' := by
  let ν' := (rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).restrict (ball (h⁻¹ • c) (R/h))
  have ha2 : ∀ j, 0 ≤ 2*a j := fun j => mul_nonneg (by norm_num) (ha j)
  letI : IsFiniteMeasure ν' := ⟨by
    change (rawPointMeasure (fun j => 2*a j) (fun j => h⁻¹ • y j)).restrict (ball (h⁻¹ • c) (R/h)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact rawPointMeasure_ball_lt_top ha2 _ _ _⟩
  have hs : Measurable (fun z : ℂ => h • z) := (continuous_const_smul h).measurable
  have hfh : Measurable (fun z : ℂ => f (h⁻¹ • z)) := hf.comp (continuous_const_smul h⁻¹).measurable
  have hF : Measurable (fun q : ℂ × ℂ => ENNReal.ofReal |f (h⁻¹ • q.1) - f (h⁻¹ • q.2)|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((hfh.comp measurable_fst).sub (hfh.comp measurable_snd)))
  change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f (h⁻¹ • q.1) - f (h⁻¹ • q.2)|
      ∂((rawPointMeasure (fun j => 2*a j) y).restrict (ball c R)).prod
        ((rawPointMeasure (fun j => 2*a j) y).restrict (ball c R))) = _
  rw [rawPointSquaredMeasure_restrict_scaling ha y hh c R]
  change (∫⁻ q : ℂ × ℂ, ENNReal.ofReal |f (h⁻¹ • q.1) - f (h⁻¹ • q.2)|
      ∂(ENNReal.ofReal (rawPointLengthScale a h ^ 2) • Measure.map (fun z : ℂ => h • z) ν').prod
        (ENNReal.ofReal (rawPointLengthScale a h ^ 2) • Measure.map (fun z : ℂ => h • z) ν')) = _
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    Measure.map_prod_map ν' ν' hs hs,lintegral_smul_measure,
    lintegral_map hF (hs.prodMap hs)]
  congr 1
  · rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  · apply lintegral_congr
    intro q
    change ENNReal.ofReal |f (h⁻¹ • (h • q.1)) - f (h⁻¹ • (h • q.2))| = _
    rw [smul_smul,smul_smul,inv_mul_cancel₀ hh.ne',one_smul,one_smul]

end RepulsiveCoulomb
