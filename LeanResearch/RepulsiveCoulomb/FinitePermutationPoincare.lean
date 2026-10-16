import LeanResearch.RepulsiveCoulomb.FiniteRegularRepresentation

/-! Literal uniform permutation Poincare inequality, exact coefficient 1/(2N). -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finite_permutation_poincare_sum {N : ℕ} (hN : 2 ≤ N)
    (f : Equiv.Perm (Fin N) → ℝ) :
    (∑ σ, (f σ - finiteUniformMean f) ^ 2) ≤
      (1 / (2 * (N : ℝ))) * ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
        ∑ σ, (f σ - f (σ * edgeTransposition s)) ^ 2 := by
  let x : EuclideanSpace ℝ (Equiv.Perm (Fin N)) := WithLp.toLp 2 f
  have h := finite_transposition_gap_norm hN finiteRightRepresentation finiteRightRepresentation_inner x
  simp only [finiteRightRepresentation_error_norm, finiteRightRepresentation_difference_norm] at h
  change 2 * (N : ℝ) * (∑ σ, (f σ - finiteUniformMean f) ^ 2) ≤
    ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
      ∑ σ, (f σ - f (σ * edgeTransposition s)) ^ 2 at h
  have hp : (0 : ℝ) < 2 * N := by positivity
  have hh : (∑ σ, (f σ - finiteUniformMean f) ^ 2) ≤
      (∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
        ∑ σ, (f σ - f (σ * edgeTransposition s)) ^ 2) / (2 * (N : ℝ)) :=
    (le_div_iff₀ hp).mpr (by nlinarith [h])
  calc
    _ ≤ _ := hh
    _ = _ := by ring

theorem finite_permutation_poincare {N : ℕ} (hN : 2 ≤ N)
    (f : Equiv.Perm (Fin N) → ℝ) :
    finiteUniformMean (fun σ => (f σ - finiteUniformMean f) ^ 2) ≤
      (1 / (2 * (N : ℝ))) * ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
        finiteUniformMean (fun σ => (f σ - f (σ * edgeTransposition s)) ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (finite_permutation_poincare_sum hN f)
    (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (Fintype.card (Equiv.Perm (Fin N)))))
  simp only [finiteUniformMean, ← Finset.mul_sum] at h ⊢
  convert h using 1 <;> ring

end RepulsiveCoulomb
