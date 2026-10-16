import LeanResearch.RepulsiveCoulomb.CoulombOneSiteFactorization

/-! Elementary symmetric-pair product identity, avoiding ordered-label assumptions. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

theorem symmetric_pair_product_sq {N : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin N → Fin N → M) (hf : ∀ i j, f i j = f j i) :
    (∏ p ∈ coulombPairs N, f p.1 p.2) ^ 2 =
      ∏ i, ∏ j, if i = j then 1 else f i j := by
  classical
  rw [coulomb_pairs_prod_double]
  have he : (∏ i, ∏ j, if j < i then f i j else 1) =
      ∏ i, ∏ j, if i < j then f i j else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    rw [hf j i]
  rw [pow_two]
  conv_lhs => rhs; rw [← he]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp [hij, not_lt_of_ge hij.le, ne_of_lt hij]
  · by_cases heq : i = j
    · subst j
      simp
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
      simp [hij, hji, heq]

theorem coulombInteraction_sq {N : ℕ} (α : ℝ) (z : CoulombConfig N) :
    coulombInteraction α z ^ 2 =
      ∏ i, ∏ j, if i = j then 1 else ‖z i - z j‖ ^ α :=
  symmetric_pair_product_sq (fun i j : Fin N => ‖z i - z j‖ ^ α) (fun i j => by rw [norm_sub_rev])

theorem coulombInteraction_nonneg {N : ℕ} (α : ℝ) (z : CoulombConfig N) :
    0 ≤ coulombInteraction α z :=
  Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)

end RepulsiveCoulomb

