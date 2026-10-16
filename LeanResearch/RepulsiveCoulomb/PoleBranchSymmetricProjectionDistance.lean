import LeanResearch.RepulsiveCoulomb.PoleBranchConjugateCancellation

/-! Exact factor-two projection-distance algebra for real centered symmetric
Gibbs L2 elements. The final conditional bridge records the missing dbar
estimate explicitly; it is not a completion of symmetric Poincare. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem poleBranch_projection_centered_residual {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) (c : ℂ) :
    (f - c • poleBranchComplexOne N hβ) -
      coulombDbarWeakProjection N hβ (f - c • poleBranchComplexOne N hβ) =
        f - coulombDbarWeakProjection N hβ f := by
  rw [map_sub, map_smul, poleBranch_weakProjection_one]
  abel

theorem poleBranch_symmetric_projection_distance {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ha2 : β / (N : ℝ) ≤ 2) (f : Lp ℂ 2 (coulombMeasure N β))
    (hreal : poleBranchComplexConj N β f = f)
    (hmean : poleBranchComplexMean N hβ f = 0)
    (hsym : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ f = f) :
    ‖f‖ ^ 2 ≤ 2 * ‖f - coulombDbarWeakProjection N hβ f‖ ^ 2 := by
  let h := coulombDbarWeakProjection N hβ f
  let u := f - h
  have hh : h ∈ coulombDbarWeakKernel N hβ := coulombDbarWeakProjection_mem_kernel hβ f
  have hhsym := poleBranch_weakProjection_invariant hβ hsym
  have hhmean : poleBranchComplexMean N hβ h = 0 := (poleBranch_weakProjection_mean hβ f).trans hmean
  have hcancel := poleBranch_weakProjection_conjugate_zero hβ ha2 h hh hhsym hhmean
  have hqu : coulombDbarWeakProjection N hβ (poleBranchComplexConj N β u) = h := by
    change coulombDbarWeakProjection N hβ (poleBranchComplexConj N β (f - h)) = h
    rw [(poleBranchComplexConj N β).map_sub, hreal,
      (coulombDbarWeakProjection N hβ).map_sub, hcancel, sub_zero]
  have hnorm : ‖h‖ ≤ ‖u‖ := by
    have H := (coulombDbarWeakKernel N hβ).toSubmodule.norm_starProjection_apply_le
      (poleBranchComplexConj N β u)
    change ‖coulombDbarWeakProjection N hβ (poleBranchComplexConj N β u)‖ ≤
      ‖poleBranchComplexConj N β u‖ at H
    simpa only [hqu, poleBranchComplexConj_norm] using H
  have ho : inner ℂ h u = 0 := by
    apply inner_eq_zero_symm.mp
    exact Submodule.starProjection_inner_eq_zero f h hh
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero h u ho
  have he : h + u = f := by dsimp only [u]; abel
  rw [he] at hp
  change ‖f‖ ^ 2 ≤ 2 * ‖u‖ ^ 2
  have hsq := pow_le_pow_left₀ (norm_nonneg h) hnorm 2
  linarith

/-- Conditional arithmetic bridge only: the literal dbar projection-distance
estimate on the original core must still be proved independently. -/
theorem poleBranch_symmetric_norm_bound_of_projection_distance
    {N : ℕ} {β E : ℝ} (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    (f : Lp ℂ 2 (coulombMeasure N β))
    (hreal : poleBranchComplexConj N β f = f)
    (hmean : poleBranchComplexMean N hβ f = 0)
    (hsym : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ f = f)
    (hdist : ‖f - coulombDbarWeakProjection N hβ f‖ ^ 2 ≤ (1 / (2 * β)) * E) :
    ‖f‖ ^ 2 ≤ (1 / β) * E := by
  calc
    _ ≤ 2 * ‖f - coulombDbarWeakProjection N hβ f‖ ^ 2 :=
      poleBranch_symmetric_projection_distance hβ ha2 f hreal hmean hsym
    _ ≤ 2 * ((1 / (2 * β)) * E) := mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = _ := by field_simp [ne_of_gt hβ] <;> ring

end RepulsiveCoulomb
