import LeanResearch.RepulsiveCoulomb.PointConformalPunctureFactor
import LeanResearch.RepulsiveCoulomb.PointFiniteOpenArgument

/-! Actual positive boundary atoms occur only at vertices of the finite
puncture-gap family, and half-open simplicity makes those vertices distinct.
The literal original weights are then coalesced at each physical vertex,
without counting a boundary atom as an interior atom or counting coincident
source locations more than once. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finite_halfOpen_simple_vertices_injective
    (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t) :
    ∀ i ≤ n, ∀ j ≤ n, f i 0 = f j 0 → i = j := by
  intro i hi j hj heq
  exact (hinj i j hi hj 0 0 (by norm_num) (by norm_num) heq).1

/-- An active source location on the boundary cannot hide in an open
puncture-free edge. Endpoint matching identifies terminal endpoints with
one of the uniquely enumerated initial vertices. -/
theorem active_location_on_finite_boundary_is_vertex
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y)
    {j : Fin m} (haj : a j ≠ 0)
    (hj : y j ∈ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) :
    ∃ k ≤ n, y j = f k 0 := by
  obtain ⟨k, hkj⟩ := mem_iUnion.mp hj
  obtain ⟨hk, hkj⟩ := mem_iUnion.mp hkj
  obtain ⟨t, ht, hty⟩ := hkj
  by_cases ht0 : t = 0
  · exact ⟨k, hk, by simpa only [ht0] using hty.symm⟩
  by_cases ht1 : t = 1
  · rw [ht1] at hty
    by_cases hkn : k = n
    · subst k
      exact ⟨0, Nat.zero_le n, hty.symm.trans hclose⟩
    · have hkn' : k < n := lt_of_le_of_ne hk hkn
      exact ⟨k + 1, Nat.succ_le_iff.mpr hkn', hty.symm.trans (hv k hkn')⟩
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  exact False.elim (havoid k hk t htI
    ⟨j, lt_of_le_of_ne (ha j) (Ne.symm haj), hty⟩)

/-- Summing the original point weights over a boundary vertex selector
produces exactly its coalesced exponent, even when locations coincide or
some nominal weights vanish. -/
theorem finite_boundary_weighted_selector_coalesces
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℕ → ℝ → ℂ) (n : ℕ) (θ : ℕ → ℝ) :
    (∑ j, (a j / 2) * (∑ k ∈ Finset.range (n + 1),
      if y j = f k 0 then θ k else 0)) =
      ∑ k ∈ Finset.range (n + 1), (coalescedPointExponent a y (f k 0) / 2) * θ k := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coalescedPointExponent_eq_sum_ite ha, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases heq : y j = f k 0 <;> simp [heq]

/-- At a genuine vertex exactly one selector survives, derived from actual
joint half-open simplicity. -/
theorem finite_boundary_selector_eq_vertex_angle
    (f : ℕ → ℝ → ℂ) (n : ℕ) (θ : ℕ → ℝ)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    {k : ℕ} (hk : k ≤ n) :
    (∑ i ∈ Finset.range (n + 1), if f k 0 = f i 0 then θ i else 0) = θ k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    have hki : f k 0 ≠ f i 0 := by
      intro heq
      exact hik (finite_halfOpen_simple_vertices_injective f n hinj k hk i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) heq).symm
    simp [hki]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)))

/-- A point outside the carrier contributes no boundary selector. -/
theorem finite_boundary_selector_zero_of_not_mem_carrier
    (f : ℕ → ℝ → ℂ) (n : ℕ) (θ : ℕ → ℝ) {w : ℂ}
    (hw : w ∉ ⋃ i ≤ n, f i '' Icc (0 : ℝ) 1) :
    (∑ i ∈ Finset.range (n + 1), if w = f i 0 then θ i else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hwi : w ≠ f i 0 := by
    intro heq
    apply hw
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
      ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hi), ⟨0, by norm_num, heq.symm⟩⟩⟩
  simp [hwi]

end RepulsiveCoulomb
