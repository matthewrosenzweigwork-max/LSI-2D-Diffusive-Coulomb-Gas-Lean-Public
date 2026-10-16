import LeanResearch.RepulsiveCoulomb.MetricRegionPathDistance
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.IntermediateValue

/-! A real midpoint of the actual variation length of any continuous finite
constrained path. No Lipschitz or Euclidean rectifiability assumption is added. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X] {P : Set X} {x z : X}

theorem MetricRegionLengthPath.exists_length_bisection
    (γ : MetricRegionLengthPath P x z) (hfin : γ.length ≠ ⊤) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      (eVariationOn γ.toFun (Icc (0 : ℝ) t)).toReal = γ.length.toReal / 2 ∧
      (eVariationOn γ.toFun (Icc t (1 : ℝ))).toReal = γ.length.toReal / 2 := by
  have hb : BoundedVariationOn γ.toFun (Icc (0 : ℝ) 1) := hfin
  let F := variationOnFromTo γ.toFun (Icc (0 : ℝ) 1) 0
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hb.continuousWithinAt_variationOnFromTo_iff (by norm_num) ht).mpr
      (γ.continuous.continuousAt.continuousWithinAt)
  have hF0 : F 0 = 0 := variationOnFromTo.self _ _ _
  have hF1 : F 1 = γ.length.toReal := by
    simp only [F, variationOnFromTo.eq_of_le _ _ (by norm_num : (0 : ℝ) ≤ 1),
      inter_self, MetricRegionLengthPath.length]
  have hhalf : γ.length.toReal / 2 ∈ Icc (F 0) (F 1) := by
    rw [hF0, hF1]
    constructor <;> linarith [ENNReal.toReal_nonneg (a := γ.length)]
  obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hF hhalf
  have hleft : (eVariationOn γ.toFun (Icc (0 : ℝ) t)).toReal = γ.length.toReal / 2 := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
    simpa only [F, variationOnFromTo.eq_of_le _ _ ht.1, inter_eq_right.mpr hsub] using hFt
  have hleftfin : eVariationOn γ.toFun (Icc (0 : ℝ) t) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eVariationOn.mono γ.toFun (Icc_subset_Icc le_rfl ht.2))
  have hrightfin : eVariationOn γ.toFun (Icc t (1 : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (eVariationOn.mono γ.toFun (Icc_subset_Icc ht.1 le_rfl))
  have hadd : eVariationOn γ.toFun (Icc (0 : ℝ) t) + eVariationOn γ.toFun (Icc t (1 : ℝ)) =
      γ.length := by
    simpa only [univ_inter, MetricRegionLengthPath.length] using
      eVariationOn.Icc_add_Icc γ.toFun (s := univ) ht.1 ht.2 (mem_univ t)
  have hadd' := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hleftfin hrightfin, hleft] at hadd'
  exact ⟨t, ht, hleft, by linarith⟩

end RepulsiveCoulomb
