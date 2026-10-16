module

public import LeanResearch.RepulsiveCoulomb.CoulombValueMean
public import LeanResearch.RepulsiveCoulomb.FiniteUnitaryAverage

@[expose] public section

/-! Literal permutation symmetrizer, orthogonal decomposition and Gibbs variance. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombSymmetrizer (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (coulombMeasure N β) →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  finiteUnitaryAverage (coulombValueRepresentation N hβ)

theorem coulombSymmetrizer_apply (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombSymmetrizer N hβ v = (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), coulombValuePermuteL N hβ σ v :=
  finiteUnitaryAverage_apply (coulombValueRepresentation N hβ) v

theorem coulombSymmetrizer_coe (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombSymmetrizer N hβ v =ᵐ[coulombMeasure N β] fun z =>
      (Nat.factorial N : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), v (coulombPermute σ z) := by
  let C : ℝ := (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹
  have hall : ∀ᵐ z ∂coulombMeasure N β, ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ v z = v (coulombPermute σ z) :=
    ae_all_iff.mpr (fun σ => coulombValuePermuteL_coe N hβ σ v)
  rw [coulombSymmetrizer_apply]
  filter_upwards [Lp.coeFn_smul C (∑ σ : Equiv.Perm (Fin N), coulombValuePermuteL N hβ σ v),
    Lp.coeFn_finsetSum Finset.univ (fun σ : Equiv.Perm (Fin N) => coulombValuePermuteL N hβ σ v), hall] with z hs hsum hall
  change (C • ∑ σ : Equiv.Perm (Fin N), coulombValuePermuteL N hβ σ v) z = _
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  simp only [Finset.sum_apply, hall]
  simp only [C, Fintype.card_perm, Fintype.card_fin]

theorem coulombSymmetrizer_invariant (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) (v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombValuePermuteL N hβ σ (coulombSymmetrizer N hβ v) = coulombSymmetrizer N hβ v :=
  finiteUnitaryAverage_invariant (coulombValueRepresentation N hβ) σ v

theorem coulombSymmetrizer_idempotent (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombSymmetrizer N hβ (coulombSymmetrizer N hβ v) = coulombSymmetrizer N hβ v :=
  finiteUnitaryAverage_idempotent (coulombValueRepresentation N hβ) v

theorem coulombSymmetrizer_selfAdjoint (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v w : Lp ℝ 2 (coulombMeasure N β)) :
    inner ℝ (coulombSymmetrizer N hβ v) w = inner ℝ v (coulombSymmetrizer N hβ w) :=
  finiteUnitaryAverage_selfAdjoint (coulombValueRepresentation N hβ) (coulombValueRepresentation_inner N hβ) v w

theorem coulombSymmetrizer_norm_decomposition (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    ‖v‖ ^ 2 = ‖coulombSymmetrizer N hβ v‖ ^ 2 + ‖v - coulombSymmetrizer N hβ v‖ ^ 2 :=
  finiteUnitaryAverage_norm_decomposition (coulombValueRepresentation N hβ)
    (coulombValueRepresentation_inner N hβ) v

theorem coulombSymmetrizer_mean (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure (N + 2) β)) :
    coulombValueMeanL N hβ (coulombSymmetrizer (N + 2) hβ v) = coulombValueMeanL N hβ v := by
  have hc : (Fintype.card (Equiv.Perm (Fin (N + 2))) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [coulombSymmetrizer_apply, map_smul, map_sum]
  simp_rw [coulombValueMeanL_permute]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem coulombSymmetrizer_variance_decomposition (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure (N + 2) β)) :
    variance (v : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) =
      variance (coulombSymmetrizer (N + 2) hβ v : CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) +
        ‖v - coulombSymmetrizer (N + 2) hβ v‖ ^ 2 := by
  rw [coulombValue_variance_eq_norm_mean N hβ, coulombValue_variance_eq_norm_mean N hβ,
    coulombSymmetrizer_mean]
  have h := coulombSymmetrizer_norm_decomposition (N + 2) hβ v
  linarith

end RepulsiveCoulomb

