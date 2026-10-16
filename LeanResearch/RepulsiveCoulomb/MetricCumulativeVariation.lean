module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Scalar cumulative variation of a Lipschitz metric-valued curve.  Its
increments dominate metric displacement, and it has the same Lipschitz
constant as the curve.  This is an actual partition-variation construction. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace RepulsiveCoulomb

theorem lipschitz_eVariationOn_Icc_le {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {s t : ℝ} {K : NNReal}
    (hγ : LipschitzOnWith K γ (Icc s t)) :
    eVariationOn γ (Icc s t) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (t - s) := by
  simpa only [Function.comp_id, eVariationOn_id_Icc] using
    hγ.comp_eVariationOn_le (mapsTo_id (Icc s t))

theorem lipschitz_boundedVariationOn_Icc {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {s t : ℝ} {K : NNReal}
    (hγ : LipschitzOnWith K γ (Icc s t)) : BoundedVariationOn γ (Icc s t) :=
  ne_top_of_le_ne_top (by finiteness) (lipschitz_eVariationOn_Icc_le hγ)

theorem metric_dist_le_cumulative_sub {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {s t u v : ℝ} (hγ : BoundedVariationOn γ (Icc s t))
    (hs : s ≤ t) (hu : u ∈ Icc s t) (hv : v ∈ Icc s t) (huv : u ≤ v) :
    dist (γ u) (γ v) ≤ variationOnFromTo γ (Icc s t) s v -
      variationOnFromTo γ (Icc s t) s u := by
  rw [variationOnFromTo.sub_right hγ.locallyBoundedVariationOn ⟨le_rfl, hs⟩ hv hu,
    variationOnFromTo.eq_of_le _ _ huv, dist_edist]
  apply ENNReal.toReal_mono (hγ.mono inter_subset_left)
  exact eVariationOn.edist_le γ ⟨hu, le_rfl, huv⟩ ⟨hv, huv, le_rfl⟩

theorem exists_lipschitz_metric_cumulative {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {s t : ℝ} {K : NNReal}
    (hγ : LipschitzOnWith K γ (Icc s t)) (hst : s ≤ t) :
    ∃ f : ℝ → ℝ, LipschitzOnWith K f (Icc s t) ∧ MonotoneOn f (Icc s t) ∧
      f s = 0 ∧ f t = (eVariationOn γ (Icc s t)).toReal ∧
      ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, dist (γ u) (γ v) ≤ dist (f u) (f v) := by
  let f : ℝ → ℝ := variationOnFromTo γ (Icc s t) s
  have hb := lipschitz_boundedVariationOn_Icc hγ
  have hm : MonotoneOn f (Icc s t) :=
    variationOnFromTo.monotoneOn hb.locallyBoundedVariationOn ⟨le_rfl, hst⟩
  have hfbound (u v : ℝ) (hu : u ∈ Icc s t) (hv : v ∈ Icc s t) (huv : u ≤ v) :
      f v - f u ≤ (K : ℝ) * (v - u) := by
    have hsub : Icc u v ⊆ Icc s t := Icc_subset_Icc hu.1 hv.2
    have hfin : (K : ℝ≥0∞) * ENNReal.ofReal (v - u) ≠ ⊤ := by finiteness
    have h := ENNReal.toReal_mono hfin (lipschitz_eVariationOn_Icc_le (hγ.mono hsub))
    simpa only [f, variationOnFromTo.sub_right hb.locallyBoundedVariationOn ⟨le_rfl, hst⟩ hv hu,
      variationOnFromTo.eq_of_le _ _ huv, inter_eq_right.mpr hsub,
      ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)] using h
  have hf : LipschitzOnWith K f (Icc s t) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rcases le_total u v with huv | hvu
    · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm hu hv huv)),
        Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact hfbound u v hu hv huv
    · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hv hu hvu)),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact hfbound v u hv hu hvu
  refine ⟨f, hf, hm, variationOnFromTo.self _ _ _, ?_, ?_⟩
  · simp only [f, variationOnFromTo.eq_of_le _ _ hst, inter_self]
  · intro u hu v hv
    rcases le_total u v with huv | hvu
    · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm hu hv huv))]
      exact metric_dist_le_cumulative_sub hb hst hu hv huv
    · rw [dist_comm (γ u), Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (hm hv hu hvu))]
      exact metric_dist_le_cumulative_sub hb hst hv hu hvu

end RepulsiveCoulomb
