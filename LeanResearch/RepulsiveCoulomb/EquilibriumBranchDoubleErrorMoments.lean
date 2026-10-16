import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceErrorMoments
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! Actual Jensen/Fubini transfer of the checked planar error moments to the
second circle average. The double error proxy equals g-P^2g only off the spatial
diagonal. Its moments are temperature-uniform under the constructed reference. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

def equilibriumAveragedCircularError (ε : ℝ) (c y : ℂ) : ℝ :=
  ∫ z : ℂ, equilibriumCircularError ε (z - y) ∂equilibriumCircleMeasure c ε

def equilibriumDoubleCircularError (ε : ℝ) (x y : ℂ) : ℝ :=
  equilibriumCircularError ε (x - y) + equilibriumAveragedCircularError ε x y

theorem equilibriumAveragedCircularError_nonneg (ε : ℝ) (c y : ℂ) :
    0 ≤ equilibriumAveragedCircularError ε c y :=
  integral_nonneg (fun z => equilibriumCircularError_nonneg ε (z - y))

theorem equilibriumAveragedCircularError_measurable (ε : ℝ) (c : ℂ) :
    Measurable (equilibriumAveragedCircularError ε c) := by
  have hm : Measurable (fun p : ℂ × ℂ => equilibriumCircularError ε (p.2 - p.1)) :=
    (equilibriumCircularError_measurable ε).comp (measurable_snd.sub measurable_fst)
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := equilibriumCircleMeasure c ε)).measurable

/-- Jensen is used only on rows whose higher angular moment is actually
integrable; that full-measure set is derived from the product bound. -/
theorem equilibriumReference_averaged_error_power {β : ℝ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (c : ℂ) :
    Integrable (fun y : ℂ => equilibriumAveragedCircularError ε c y ^ p) R.measure ∧
      (∫ y : ℂ, equilibriumAveragedCircularError ε c y ^ p ∂R.measure) ≤
        2 * (p.factorial : ℝ) * ε ^ 2 := by
  have hF := equilibriumReference_circle_error_power_integrable R hε p hp c
  have hj : ∀ᵐ y ∂(R.measure : Measure ℂ), equilibriumAveragedCircularError ε c y ^ p ≤
      ∫ z : ℂ, equilibriumCircularError ε (z - y) ^ p ∂equilibriumCircleMeasure c ε := by
    filter_upwards [hF.prod_left_ae] with y hy
    exact (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
      (Eventually.of_forall (fun z => equilibriumCircularError_nonneg ε (z - y)))
      (equilibriumCircularError_circle_integrable hε c y) hy
  have hi : Integrable (fun y : ℂ => equilibriumAveragedCircularError ε c y ^ p) R.measure := by
    apply hF.integral_prod_right.mono'
      ((equilibriumAveragedCircularError_measurable ε c).pow_const p).aestronglyMeasurable
    filter_upwards [hj] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pow_nonneg (equilibriumAveragedCircularError_nonneg ε c y) p)]
    exact hy
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi hF.integral_prod_right hj
  have hs := integral_integral_swap
    (f := fun (z y : ℂ) => equilibriumCircularError ε (z - y) ^ p) hF
  rw [← hs] at h
  have hm := integral_mono hF.integral_prod_left (integrable_const (2 * (p.factorial : ℝ) * ε ^ 2))
    (equilibriumReference_error_power_bound R hε p hp)
  simp only [integral_const, probReal_univ, one_smul] at hm
  exact h.trans hm

theorem equilibriumDoubleCircularError_nonneg (ε : ℝ) (x y : ℂ) :
    0 ≤ equilibriumDoubleCircularError ε x y :=
  add_nonneg (equilibriumCircularError_nonneg ε _) (equilibriumAveragedCircularError_nonneg ε x y)

theorem equilibriumDoubleCircularError_measurable (ε : ℝ) (x : ℂ) :
    Measurable (equilibriumDoubleCircularError ε x) :=
  ((equilibriumCircularError_measurable ε).comp (measurable_const.sub measurable_id)).add
    (equilibriumAveragedCircularError_measurable ε x)

/-- Actual all-positive-integer error moments, uniform in beta and the fixed
particle location. The explicit coefficient is 2^(p-1)*4*p!. -/
theorem equilibriumReference_double_error_power {β : ℝ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (x : ℂ) :
    Integrable (fun y : ℂ => equilibriumDoubleCircularError ε x y ^ p) R.measure ∧
      (∫ y : ℂ, equilibriumDoubleCircularError ε x y ^ p ∂R.measure) ≤
        (2 : ℝ) ^ (p - 1) * 4 * (p.factorial : ℝ) * ε ^ 2 := by
  have hsingle := equilibriumReference_error_power_integrable R hε p hp x
  obtain ⟨havg, havgbound⟩ := equilibriumReference_averaged_error_power R hε p hp x
  have hmajor := (hsingle.add havg).const_mul ((2 : ℝ) ^ (p - 1))
  have hpoint (y : ℂ) : equilibriumDoubleCircularError ε x y ^ p ≤
      (2 : ℝ) ^ (p - 1) * (equilibriumCircularError ε (x - y) ^ p +
        equilibriumAveragedCircularError ε x y ^ p) :=
    add_pow_le (equilibriumCircularError_nonneg ε _) (equilibriumAveragedCircularError_nonneg ε x y) p
  have hi : Integrable (fun y : ℂ => equilibriumDoubleCircularError ε x y ^ p) R.measure := by
    apply hmajor.mono' ((equilibriumDoubleCircularError_measurable ε x).pow_const p).aestronglyMeasurable
    exact Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (equilibriumDoubleCircularError_nonneg ε x y) p)]
      exact hpoint y)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hsingle havg] at h
  have hs := equilibriumReference_error_power_bound R hε p hp x
  have hb := mul_le_mul_of_nonneg_left (add_le_add hs havgbound)
    (by positivity : 0 ≤ (2 : ℝ) ^ (p - 1))
  apply h.trans (hb.trans_eq ?_)
  ring

/-- The error identity is deliberately restricted to distinct spatial points. -/
theorem equilibriumDoubleCircularError_eq_sub {ε : ℝ} (hε : 0 < ε)
    {x y : ℂ} (hxy : x ≠ y) :
    equilibriumDoubleCircularError ε x y =
      equilibriumLogKernel (x - y) - equilibriumDoubleCircularKernel ε x y :=
  (equilibriumLogKernel_sub_double hε hxy).symm

end RepulsiveCoulomb
