module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Tactic

@[expose] public section

/-! Exact double layer cake using strict lower/upper level sets. The identity
requires no atomlessness of the image law and holds in ENNReal before integrability. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

variable {X : Type*} [MeasurableSpace X]

def thresholdPairSet (f : X → ℝ) (t : ℝ) : Set (X × X) :=
  ({x | f x < t} ×ˢ {x | t < f x}) ∪ ({x | t < f x} ×ˢ {x | f x < t})

theorem thresholdPairSet_measurable {f : X → ℝ} (hf : Measurable f) (t : ℝ) :
    MeasurableSet (thresholdPairSet f t) :=
  ((measurableSet_lt hf measurable_const).prod (measurableSet_lt measurable_const hf)).union
    ((measurableSet_lt measurable_const hf).prod (measurableSet_lt hf measurable_const))

theorem thresholdPairSet_measure {f : X → ℝ} (hf : Measurable f) (ν : Measure X) [SFinite ν] (t : ℝ) :
    (ν.prod ν) (thresholdPairSet f t) = 2 * (ν {x | f x < t} * ν {x | t < f x}) := by
  have hd : Disjoint ({x | f x < t} ×ˢ {x | t < f x}) ({x | t < f x} ×ˢ {x | f x < t}) := by
    apply Set.disjoint_left.mpr
    intro q hq hq'
    have ha : f q.1 < t := hq.1
    have hb : t < f q.1 := hq'.1
    exact not_lt_of_ge hb.le ha
  rw [thresholdPairSet, measure_union hd
    ((measurableSet_lt measurable_const hf).prod (measurableSet_lt hf measurable_const)),
    Measure.prod_prod, Measure.prod_prod]
  ring

theorem thresholdPairSet_parameter_integral (f : X → ℝ) (q : X × X) :
    (∫⁻ t : ℝ, (thresholdPairSet f t).indicator 1 q) = ENNReal.ofReal |f q.1 - f q.2| := by
  have heq : (fun t : ℝ => (thresholdPairSet f t).indicator (1 : X × X → ℝ≥0∞) q) =
      (uIoo (f q.1) (f q.2)).indicator 1 := by
    funext t
    simp only [thresholdPairSet, uIoo_eq_union, Set.indicator_apply, mem_union, mem_prod, mem_setOf_eq, mem_Ioo]
    congr 1
    apply propext
    tauto
  rw [heq, lintegral_indicator_one (show MeasurableSet (uIoo (f q.1) (f q.2)) from measurableSet_Ioo), Real.volume_uIoo, abs_sub_comm]

theorem thresholdPairSet_kernel_measurable {f : X → ℝ} (hf : Measurable f) :
    Measurable (fun q : (X × X) × ℝ => (thresholdPairSet f q.2).indicator (1 : X × X → ℝ≥0∞) q.1) := by
  have h1 : MeasurableSet {q : (X × X) × ℝ | f q.1.1 < q.2} := measurableSet_lt (hf.comp (measurable_fst.comp measurable_fst)) measurable_snd
  have h2 : MeasurableSet {q : (X × X) × ℝ | q.2 < f q.1.2} := measurableSet_lt measurable_snd (hf.comp (measurable_snd.comp measurable_fst))
  have h3 : MeasurableSet {q : (X × X) × ℝ | q.2 < f q.1.1} := measurableSet_lt measurable_snd (hf.comp (measurable_fst.comp measurable_fst))
  have h4 : MeasurableSet {q : (X × X) × ℝ | f q.1.2 < q.2} := measurableSet_lt (hf.comp (measurable_snd.comp measurable_fst)) measurable_snd
  have hh := (measurable_const : Measurable (fun _ : (X × X) × ℝ => (1 : ℝ≥0∞))).indicator
    ((h1.inter h2).union (h3.inter h4))
  convert hh using 1
  funext q
  simp only [thresholdPairSet, Set.indicator_apply, mem_union, mem_inter_iff, mem_prod, mem_setOf_eq]
  rfl

theorem double_layer_cake_prod {f : X → ℝ} (hf : Measurable f) (ν : Measure X) [SFinite ν] :
    (∫⁻ q : X × X, ENNReal.ofReal |f q.1 - f q.2| ∂ν.prod ν) =
      2 * ∫⁻ t : ℝ, ν {x | f x < t} * ν {x | t < f x} := by
  calc
    _ = ∫⁻ q : X × X, (∫⁻ t : ℝ, (thresholdPairSet f t).indicator 1 q ∂volume) ∂ν.prod ν :=
      lintegral_congr (fun q => (thresholdPairSet_parameter_integral f q).symm)
    _ = ∫⁻ t : ℝ, ∫⁻ q : X × X, (thresholdPairSet f t).indicator 1 q ∂ν.prod ν :=
      lintegral_lintegral_swap (thresholdPairSet_kernel_measurable hf).aemeasurable
    _ = ∫⁻ t : ℝ, 2 * (ν {x | f x < t} * ν {x | t < f x}) := by
      apply lintegral_congr
      intro t
      rw [lintegral_indicator_one (thresholdPairSet_measurable hf t), thresholdPairSet_measure hf ν t]
    _ = _ := lintegral_const_mul' 2 _ (by norm_num)

end RepulsiveCoulomb
