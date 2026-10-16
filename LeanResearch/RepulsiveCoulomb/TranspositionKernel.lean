module

public import LeanResearch.RepulsiveCoulomb.TranspositionBochner

@[expose] public section

/-! Kernel identification by positivity and transposition generation. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem transpositionLaplacian_kernel_invariant
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y)
    (x : E) (hx : transpositionLaplacian U x = 0) (σ : Equiv.Perm (Fin N)) : U σ x = x := by
  have hz : (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
      inner ℝ x (unitaryDifference U (edgeTransposition s) x)) = 0 := by
    rw [← inner_sum, ← transpositionLaplacian_apply, hx, inner_zero_right]
  have hswap (i j : Fin N) (hij : i ≠ j) : U (Equiv.swap i j) x = x := by
    have hs : ({i,j} : Finset (Fin N)) ∈ Finset.univ.powersetCard 2 := by
      simp [Finset.mem_powersetCard, hij]
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => unitaryDifference_positive U hU (edgeTransposition s) x)).mp hz _ hs
    rw [edgeTransposition_pair i j hij] at he
    have hen := unitaryDifference_energy U hU (Equiv.swap i j) x
    rw [he, mul_zero] at hen
    have hd : unitaryDifference U (Equiv.swap i j) x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (unitaryDifference U (Equiv.swap i j) x)]
    exact (sub_eq_zero.mp hd).symm
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul σ i j hij ih =>
      rw [map_mul]
      change U (Equiv.swap i j) (U σ x) = x
      rw [ih, hswap i j hij]

theorem finiteUnitaryAverage_of_invariant {G : Type*} [Group G] [Fintype G]
    (U : G →* (E →L[ℝ] E)) (x : E) (hx : ∀ g, U g x = x) :
    finiteUnitaryAverage U x = x := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [finiteUnitaryAverage_apply]
  simp_rw [hx]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem transpositionLaplacian_average
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E)) (x : E) :
    transpositionLaplacian U (finiteUnitaryAverage U x) = 0 := by
  simp only [transpositionLaplacian_apply, unitaryDifference_apply,
    finiteUnitaryAverage_invariant, sub_self, Finset.sum_const_zero]

theorem transpositionLaplacian_kernel_average
    (U : Equiv.Perm (Fin N) →* (E →L[ℝ] E))
    (hU : ∀ g x y, inner ℝ (U g x) (U g y) = inner ℝ x y)
    (x : E) (hx : transpositionLaplacian U x = 0) : finiteUnitaryAverage U x = x :=
  finiteUnitaryAverage_of_invariant U x (transpositionLaplacian_kernel_invariant U hU x hx)

end RepulsiveCoulomb
