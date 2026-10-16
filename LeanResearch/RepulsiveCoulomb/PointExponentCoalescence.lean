import LeanResearch.RepulsiveCoulomb.RawPointVolumeGrowth

/-! Reduction to distinct positive-exponent locations, as required by Bonk--Lang,
*Bi-Lipschitz parameterization of surfaces* (2003), Theorem 9.1, p. 168.
This is only the finite algebraic reduction, not a formalization or assumption of
that theorem. Coincident points are merged exactly; zero exponents are omitted. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The finite set of actual puncture locations. -/
def positivePointLocations {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Finset ℂ := by
  classical
  exact (positivePointIndices a).image y

@[simp] theorem mem_positivePointLocations {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (p : ℂ) :
    p ∈ positivePointLocations a y ↔ ∃ j, 0 < a j ∧ y j = p := by
  classical
  simp [positivePointLocations]

/-- Total positive exponent at one location. -/
def coalescedPointExponent {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) : ℝ := by
  classical
  exact ∑ j ∈ (positivePointIndices a).filter (fun j ↦ y j = p), a j

theorem coalescedPointExponent_nonneg {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (p : ℂ) : 0 ≤ coalescedPointExponent a y p := by
  classical
  apply Finset.sum_nonneg
  intro j hj
  exact ((mem_positivePointIndices a j).mp (Finset.mem_filter.mp hj).1).le

theorem coalescedPointExponent_pos {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) {p : ℂ} (hp : p ∈ positivePointLocations a y) :
    0 < coalescedPointExponent a y p := by
  classical
  obtain ⟨j, hj, hloc⟩ := (mem_positivePointLocations a y p).mp hp
  apply Finset.sum_pos'
  · intro k hk
    exact ((mem_positivePointIndices a k).mp (Finset.mem_filter.mp hk).1).le
  · exact ⟨j, Finset.mem_filter.mpr ⟨(mem_positivePointIndices a j).mpr hj, hloc⟩, hj⟩

theorem sum_positivePointIndices {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) : ∑ j ∈ positivePointIndices a, a j = ∑ j, a j := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hn : ¬ 0 < a j := by simpa using hj
  exact le_antisymm (le_of_not_gt hn) (ha j)

theorem sum_coalescedPointExponent {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∑ p ∈ positivePointLocations a y, coalescedPointExponent a y p = ∑ j, a j := by
  classical
  unfold coalescedPointExponent positivePointLocations
  rw [Finset.sum_fiberwise_of_maps_to (fun j hj ↦ Finset.mem_image_of_mem y hj)]
  exact sum_positivePointIndices ha

theorem rawPointWeight_eq_positive_product {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    rawPointWeight a y z = ∏ j ∈ positivePointIndices a, ‖z - y j‖ ^ a j := by
  classical
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro j _ hj
  have hz : a j = 0 := le_antisymm (le_of_not_gt (by simpa using hj)) (ha j)
  simp [hz]

/-- Pointwise, including at punctures: merging coincident points preserves the weight. -/
theorem rawPointWeight_eq_coalesced_product {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    rawPointWeight a y z = ∏ p ∈ positivePointLocations a y,
      ‖z - p‖ ^ coalescedPointExponent a y p := by
  classical
  rw [rawPointWeight_eq_positive_product ha]
  symm
  calc
    _ = ∏ p ∈ positivePointLocations a y,
        ∏ j ∈ (positivePointIndices a).filter (fun j ↦ y j = p), ‖z - y j‖ ^ a j := by
      apply Finset.prod_congr rfl
      intro p _
      rw [coalescedPointExponent, Real.rpow_sum_of_nonneg (norm_nonneg _)
        (fun j _ ↦ ha j)]
      apply Finset.prod_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := Finset.prod_fiberwise_of_maps_to
      (fun j hj ↦ Finset.mem_image_of_mem y hj) _

theorem positivePointLocations_eq_punctures {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) : (positivePointLocations a y : Set ℂ) = pointPunctures a y := by
  ext p
  simp only [Finset.mem_coe, mem_positivePointLocations, pointPunctures, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, h.symm⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, h.symm⟩

/-- A distinct family indexed by the actual positive locations. -/
def coalescedPointLocation {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (p : ↥(positivePointLocations a y)) : ℂ := p.val

theorem coalescedPointLocation_injective {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    Function.Injective (coalescedPointLocation a y) := Subtype.val_injective

theorem coalescedPointExponent_sum_le {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    ∑ p ∈ positivePointLocations a y, coalescedPointExponent a y p ≤ Q := by
  rw [sum_coalescedPointExponent ha]
  exact hQ

/-- Bonk--Lang's distinct-point input loses neither total exponent nor any weight value. -/
theorem exists_distinct_positive_point_representation {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ n : ℕ, ∃ b : Fin n → ℝ, ∃ p : Fin n → ℂ,
      (∀ j, 0 < b j) ∧ Function.Injective p ∧
      (∑ j, b j = ∑ j, a j) ∧ rawPointWeight b p = rawPointWeight a y := by
  classical
  let S := positivePointLocations a y
  let e : Fin (Fintype.card ↥S) ≃ ↥S := (Fintype.equivFin ↥S).symm
  let b := fun j ↦ coalescedPointExponent a y (e j).val
  let p := fun j ↦ (e j).val
  refine ⟨Fintype.card ↥S, b, p, ?_, ?_, ?_, ?_⟩
  · intro j
    exact coalescedPointExponent_pos a y (e j).property
  · exact Subtype.val_injective.comp e.injective
  · change (∑ j, coalescedPointExponent a y (e j).val) = _
    rw [Fintype.sum_equiv e _ (fun x ↦ coalescedPointExponent a y x.val) (fun _ ↦ rfl)]
    simpa only [S, Finset.sum_coe_sort] using sum_coalescedPointExponent ha y
  · funext z
    unfold rawPointWeight
    change (∏ j, ‖z - (e j).val‖ ^ coalescedPointExponent a y (e j).val) = _
    rw [Fintype.prod_equiv e _
      (fun x ↦ ‖z - x.val‖ ^ coalescedPointExponent a y x.val) (fun _ ↦ rfl)]
    exact (Finset.prod_coe_sort S (fun x ↦ ‖z - x‖ ^ coalescedPointExponent a y x)).trans
      (rawPointWeight_eq_coalesced_product ha y z).symm

end RepulsiveCoulomb
