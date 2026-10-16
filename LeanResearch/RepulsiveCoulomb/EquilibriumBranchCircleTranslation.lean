module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDoubleCircular

@[expose] public section

/-! Exact translated circle laws, used to keep the circle of integration fixed
in parameter measurability and to identify every double-smoothed energy term. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumCircleMeasure_translate (ε : ℝ) (x : ℂ) :
    Measure.map (fun z : ℂ => z + x) (equilibriumCircleMeasure 0 ε) = equilibriumCircleMeasure x ε := by
  have hm : Measurable (fun z : ℂ => z + x) := measurable_id.add measurable_const
  unfold equilibriumCircleMeasure
  rw [Measure.map_map hm (measurable_circleMap 0 ε)]
  congr 1
  funext θ
  simp only [Function.comp_apply, circleMap, zero_add, add_zero, add_comm]

theorem integral_equilibriumCircleMeasure_translate (ε : ℝ) (x : ℂ) {f : ℂ → ℝ}
    (hf : Measurable f) :
    (∫ z : ℂ, f (z + x) ∂equilibriumCircleMeasure 0 ε) =
      ∫ z : ℂ, f z ∂equilibriumCircleMeasure x ε := by
  have hm : Measurable (fun z : ℂ => z + x) := measurable_id.add measurable_const
  rw [← equilibriumCircleMeasure_translate ε x,
    integral_map hm.aemeasurable hf.aestronglyMeasurable]

theorem equilibriumDoubleCircularKernel_translate {ε : ℝ} (hε : 0 < ε) (x y : ℂ) :
    equilibriumDoubleCircularKernel ε x y =
      ∫ z : ℂ, equilibriumCircularKernel ε (z + x - y) ∂equilibriumCircleMeasure 0 ε :=
  (integral_equilibriumCircleMeasure_translate ε x
    ((equilibriumCircularKernel_continuous hε).measurable.comp
      (measurable_id.sub measurable_const))).symm

/-- Joint measurability of the genuine double kernel, including its finite
self-energy diagonal. -/
theorem equilibriumDoubleCircularKernel_joint_measurable {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun p : ℂ × ℂ => equilibriumDoubleCircularKernel ε p.1 p.2) := by
  have hm : Measurable (fun q : (ℂ × ℂ) × ℂ =>
      equilibriumCircularKernel ε (q.2 + q.1.1 - q.1.2)) :=
    (equilibriumCircularKernel_continuous hε).measurable.comp
      ((measurable_snd.add (measurable_fst.comp measurable_fst)).sub (measurable_snd.comp measurable_fst))
  have h := (hm.stronglyMeasurable.integral_prod_right'
    (ν := equilibriumCircleMeasure 0 ε)).measurable
  simpa only [equilibriumDoubleCircularKernel_translate hε] using h

end RepulsiveCoulomb
