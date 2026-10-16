import LeanResearch.RepulsiveCoulomb.PointActualBalancedLine
import LeanResearch.RepulsiveCoulomb.PointZeroExponentGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Uncompiled records-only successor. Join the actual positive-mass balanced
line construction with the literal Euclidean zero-mass branch, without any
new hypothesis on locations, separation or positive weights. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem exists_pointConformal_actual_curvature_balanced_line
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
        ∃ Λ : ℂ → ℝ,
          (∀ p ∈ pointLinePositiveAtomLocations a y c,
            PointLinePhysicalSideWidths a y A B p (Λ p)
              (2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p) ∧
            Real.pi ≤ Λ p ∧ Real.pi ≤ 2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p) ∧
          let νA := pointLineSignedSideCurvature a y c A Λ
          let νB := pointLineSignedSideCurvature a y c B
            (fun p => 2 * Real.pi + Real.pi * coalescedPointExponent a y p - Λ p)
          νA.support ⊆ positivePointLocations a y ∧ νB.support ⊆ positivePointLocations a y ∧
          (∀ p, νA p ≤ 0 ∧ νB p ≤ 0) ∧
          pointLineSignedSideMass a y νA = -(Real.pi * pointExteriorHalfMass a) ∧
          pointLineSignedSideMass a y νB = -(Real.pi * pointExteriorHalfMass a) ∧
          ∀ p, νA p + νB p = -(Real.pi * coalescedPointExponent a y p) := by
  by_cases hB : 0 < pointExteriorHalfMass a
  · exact exists_pointConformal_actual_curvature_balanced_line_positive ha y hB
  have hBnonneg : 0 ≤ pointExteriorHalfMass a := by
    unfold pointExteriorHalfMass
    exact Finset.sum_nonneg (fun j _ => div_nonneg (ha j) (by norm_num))
  have hBzero : pointExteriorHalfMass a = 0 := le_antisymm (le_of_not_gt hB) hBnonneg
  have hsum : ∑ j, a j = 0 := by
    have h := hBzero
    unfold pointExteriorHalfMass at h
    rw [← Finset.sum_div] at h
    linarith
  have haj : ∀ j, a j = 0 := pointExponent_eq_zero_of_sum_zero ha hsum
  have hLoc : positivePointLocations a y = ∅ := by
    ext p
    simp only [mem_positivePointLocations, Finset.notMem_empty, iff_false]
    rintro ⟨j, hj, _⟩
    rw [haj j] at hj
    exact lt_irrefl _ hj
  have hκ : ∀ p, coalescedPointExponent a y p = 0 := fun p =>
    coalescedPointExponent_eq_zero_of_not_mem a y (by rw [hLoc]; exact Finset.notMem_empty p)
  let c : ℝ → ℂ := fun t => (t : ℂ)
  have hc : Continuous c := Complex.continuous_ofReal
  have hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t := by
    intro s t
    rw [pointSmoothConformalEDist_eq_euclidean_of_sum_zero ha hsum,
      ENNReal.toReal_ofReal (norm_nonneg _), Real.dist_eq]
    simp only [c, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  obtain ⟨A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB⟩ :=
    exists_pointMetricLine_side_regions ha y c hd
  have hν (U : Set ℂ) (Λ : ℂ → ℝ) : pointLineSignedSideCurvature a y c U Λ = 0 := by
    ext p
    simp [hLoc]
  refine ⟨c, hc, hd, A, B, hA, hBo, hAc, hBc, hAB, hcover, hfA, hfB, fun _ => Real.pi, ?_, ?_⟩
  · intro p hp
    simp [pointLinePositiveAtomLocations, hLoc] at hp
  · simp only [hν, Finsupp.support_zero, Finset.empty_subset, Finsupp.coe_zero,
      Pi.zero_apply, le_refl, and_self, implies_true, pointLineSignedSideMass,
      Finset.sum_const_zero, hBzero, mul_zero, neg_zero, hκ, zero_add]

end RepulsiveCoulomb
