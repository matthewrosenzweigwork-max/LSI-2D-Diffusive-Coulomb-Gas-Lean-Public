import LeanResearch.RepulsiveCoulomb.CoulombSymmetricPairs

/-! Exact all-pair Euclidean gradient accounting. -/
noncomputable section
open scoped BigOperators
open InnerProductSpace
namespace RepulsiveCoulomb

theorem coulomb_pairs_sum_double {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ p ∈ coulombPairs N, f p.1 p.2) = ∑ i, ∑ j, if i < j then f i j else 0 := by
  classical
  rw [coulombPairs, Finset.sum_filter, Fintype.sum_prod_type]

theorem symmetric_pair_sum_twice {N : ℕ} (f : Fin N → Fin N → ℝ)
    (hf : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    2 * (∑ p ∈ coulombPairs N, f p.1 p.2) = ∑ i, ∑ j, f i j := by
  classical
  rw [coulomb_pairs_sum_double, two_mul]
  have he : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf j i]
  conv_lhs => rhs; rw [← he]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp [hij, not_lt_of_ge hij.le]
  · by_cases heq : i = j
    · subst j
      simp [hdiag]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
      simp [hij, hji]

theorem coulomb_pair_norm_sq_identity {N : ℕ} (g : CoulombConfig N) :
    (∑ p ∈ coulombPairs N, ‖g p.1 - g p.2‖ ^ 2) =
      (N : ℝ) * ‖g‖ ^ 2 - ‖∑ i, g i‖ ^ 2 := by
  have ht := symmetric_pair_sum_twice (fun i j : Fin N => ‖g i - g j‖ ^ 2)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have hi : (∑ i : Fin N, ∑ j : Fin N, inner ℝ (g i) (g j)) = ‖∑ i, g i‖ ^ 2 := by
    simp_rw [← inner_sum]
    rw [← sum_inner, real_inner_self_eq_norm_sq]
  have hd : (∑ i : Fin N, ∑ j : Fin N, ‖g i - g j‖ ^ 2) =
      2 * (N : ℝ) * (∑ i, ‖g i‖ ^ 2) - 2 * ‖∑ i, g i‖ ^ 2 := by
    simp_rw [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, hi]
    ring
  rw [hd, ← EuclideanSpace.norm_sq_eq] at ht
  linarith

theorem coulomb_pair_norm_sq_sum_le {N : ℕ} (g : CoulombConfig N) :
    (∑ p ∈ coulombPairs N, ‖g p.1 - g p.2‖ ^ 2) ≤ (N : ℝ) * ‖g‖ ^ 2 := by
  rw [coulomb_pair_norm_sq_identity]
  linarith [sq_nonneg ‖∑ i, g i‖]

end RepulsiveCoulomb

