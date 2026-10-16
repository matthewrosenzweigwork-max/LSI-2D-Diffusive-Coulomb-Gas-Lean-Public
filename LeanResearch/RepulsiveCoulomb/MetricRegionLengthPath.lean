module

public import LeanResearch.RepulsiveCoulomb.AffineCurveVariation
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Actual continuous paths in a subset, with their ambient partition-variation
length. Global representatives merely simplify concatenation; clipping gives
such a representative for every continuous path on the unit interval. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

structure MetricRegionLengthPath {X : Type*} [TopologicalSpace X]
    (P : Set X) (x z : X) where
  toFun : ℝ → X
  continuous : Continuous toFun
  source : toFun 0 = x
  target : toFun 1 = z
  mapsTo : MapsTo toFun (Icc (0 : ℝ) 1) P

namespace MetricRegionLengthPath
variable {X : Type*} [TopologicalSpace X] {P : Set X} {x y z : X}

def const (hx : x ∈ P) : MetricRegionLengthPath P x x where
  toFun := fun _ ↦ x
  continuous := continuous_const
  source := rfl
  target := rfl
  mapsTo := fun _ _ ↦ hx

def reverse (γ : MetricRegionLengthPath P x z) : MetricRegionLengthPath P z x where
  toFun := fun t ↦ γ.toFun (1 - t)
  continuous := γ.continuous.comp (continuous_const.sub continuous_id)
  source := by simpa using γ.target
  target := by simpa using γ.source
  mapsTo := by
    intro t ht
    apply γ.mapsTo
    constructor <;> linarith [ht.1, ht.2]

def subpath (γ : MetricRegionLengthPath P x z) (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    MetricRegionLengthPath P (γ.toFun s) (γ.toFun t) where
  toFun := fun u ↦ γ.toFun (s + u * (t - s))
  continuous := γ.continuous.comp (by fun_prop)
  source := by simp
  target := by simp
  mapsTo := by
    intro u hu
    apply γ.mapsTo
    have h := (affine_unitInterval_image s t ▸ mem_image_of_mem
      (fun u : ℝ ↦ s + u * (t - s)) hu : s + u * (t - s) ∈ uIcc s t)
    exact (uIcc_subset_Icc hs ht) h

def trans (γ : MetricRegionLengthPath P x y) (η : MetricRegionLengthPath P y z) :
    MetricRegionLengthPath P x z where
  toFun := fun t ↦ if t ≤ 1 / 2 then γ.toFun (2 * t) else η.toFun (2 * t - 1)
  continuous := by
    apply Continuous.if_le (γ.continuous.comp (by fun_prop))
      (η.continuous.comp (by fun_prop)) continuous_id continuous_const
    intro t ht
    change t = 1 / 2 at ht
    rw [ht]
    norm_num [γ.target, η.source]
  source := by norm_num [γ.source]
  target := by norm_num [η.target]
  mapsTo := by
    intro t ht
    change (if t ≤ 1 / 2 then γ.toFun (2 * t) else η.toFun (2 * t - 1)) ∈ P
    split_ifs with h
    · apply γ.mapsTo
      constructor <;> linarith [ht.1]
    · apply η.mapsTo
      constructor <;> linarith [ht.2]

def ofContinuousOn (f : ℝ → X) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (h0 : f 0 = x) (h1 : f 1 = z) (hP : MapsTo f (Icc (0 : ℝ) 1) P) :
    MetricRegionLengthPath P x z where
  toFun := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (fun t ↦ f t.1)
  continuous := continuous_IccExtend_iff.mpr hf.restrict
  source := (IccExtend_of_mem _ _ (by norm_num)).trans h0
  target := (IccExtend_of_mem _ _ (by norm_num)).trans h1
  mapsTo := by
    intro t ht
    rw [IccExtend_of_mem _ _ ht]
    exact hP ht

end MetricRegionLengthPath

namespace MetricRegionLengthPath
variable {X : Type*} [PseudoMetricSpace X] {P : Set X} {x y z : X}

def length (γ : MetricRegionLengthPath P x z) : ℝ≥0∞ :=
  eVariationOn γ.toFun (Icc (0 : ℝ) 1)

theorem endpoint_le_length (γ : MetricRegionLengthPath P x z) :
    edist x z ≤ γ.length := by
  simpa only [length, γ.source, γ.target] using
    eVariationOn.edist_le γ.toFun (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)

theorem length_const (hx : x ∈ P) : (const hx).length = 0 := by
  simp [length, const, eVariationOn]

theorem length_reverse (γ : MetricRegionLengthPath P x z) : γ.reverse.length = γ.length := by
  have h := eVariationOn_affine_unitInterval γ.toFun 1 0
  simpa only [length, reverse, zero_sub, mul_neg, mul_one, ← sub_eq_add_neg,
    uIcc_of_ge (by norm_num : (0 : ℝ) ≤ 1)] using h

theorem length_subpath (γ : MetricRegionLengthPath P x z) (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (γ.subpath s t hs ht).length = eVariationOn γ.toFun (uIcc s t) :=
  eVariationOn_affine_unitInterval γ.toFun s t

theorem length_ofContinuousOn (f : ℝ → X) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (h0 : f 0 = x) (h1 : f 1 = z) (hP : MapsTo f (Icc (0 : ℝ) 1) P) :
    (ofContinuousOn f hf h0 h1 hP).length = eVariationOn f (Icc (0 : ℝ) 1) := by
  apply eVariationOn.eq_of_eqOn
  intro t ht
  change IccExtend (show (0 : ℝ) ≤ 1 by norm_num) (fun u : Icc (0 : ℝ) 1 ↦ f u.1) t = f t
  exact IccExtend_of_mem _ _ ht

theorem length_trans_le (γ : MetricRegionLengthPath P x y) (η : MetricRegionLengthPath P y z) :
    (γ.trans η).length ≤ γ.length + η.length := by
  let f := (γ.trans η).toFun
  have hleft : eVariationOn f (Icc (0 : ℝ) (1 / 2)) ≤ γ.length := by
    have he : EqOn f (γ.toFun ∘ fun t : ℝ ↦ 2 * t) (Icc (0 : ℝ) (1 / 2)) := by
      intro t ht
      exact if_pos ht.2
    rw [eVariationOn.eq_of_eqOn he]
    apply eVariationOn.comp_le_of_monotoneOn γ.toFun (fun t : ℝ ↦ 2 * t)
    · intro u _ v _ huv
      linarith
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]
  have hright : eVariationOn f (Icc (1 / 2 : ℝ) 1) ≤ η.length := by
    have he : EqOn f (η.toFun ∘ fun t : ℝ ↦ 2 * t - 1) (Icc (1 / 2 : ℝ) 1) := by
      intro t ht
      change (if t ≤ 1 / 2 then γ.toFun (2 * t) else η.toFun (2 * t - 1)) = _
      by_cases h : t ≤ 1 / 2
      · have heq : t = 1 / 2 := le_antisymm h ht.1
        subst t
        norm_num [γ.target, η.source]
      · exact if_neg h
    rw [eVariationOn.eq_of_eqOn he]
    apply eVariationOn.comp_le_of_monotoneOn η.toFun (fun t : ℝ ↦ 2 * t - 1)
    · intro u _ v _ huv
      linarith
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]
  have hadd : eVariationOn f (Icc (0 : ℝ) (1 / 2)) +
      eVariationOn f (Icc (1 / 2 : ℝ) 1) = eVariationOn f (Icc (0 : ℝ) 1) := by
    simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (mem_univ _)
  change eVariationOn f (Icc (0 : ℝ) 1) ≤ γ.length + η.length
  rw [← hadd]
  exact add_le_add hleft hright

end MetricRegionLengthPath
end RepulsiveCoulomb
