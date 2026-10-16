module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelProjection
public import LeanResearch.RepulsiveCoulomb.PoleBranchPairComplexChart
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

/-! Literal complex Gibbs L2 permutation and conjugation operations for the
symmetric projection argument. These are independent of a dbar estimate. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

def poleBranchComplexPermute (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N)) :
    Lp ℂ 2 (coulombMeasure N β) →ₗᵢ[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  Lp.compMeasurePreservingₗᵢ ℂ (coulombPermute σ) (coulombPermute_gibbs_preserving hβ.le σ)

theorem poleBranchComplexPermute_coe {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexPermute N hβ σ v =ᵐ[coulombMeasure N β] fun z => v (coulombPermute σ z) :=
  Lp.coeFn_compMeasurePreserving v (coulombPermute_gibbs_preserving hβ.le σ)

theorem poleBranchComplexPermute_inverse {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexPermute N hβ σ.symm (poleBranchComplexPermute N hβ σ v) = v := by
  have ht := (coulombPermute_gibbs_preserving hβ.le σ.symm).quasiMeasurePreserving.ae
    (poleBranchComplexPermute_coe hβ σ v)
  apply Lp.ext
  filter_upwards [poleBranchComplexPermute_coe hβ σ.symm (poleBranchComplexPermute N hβ σ v), ht]
    with z hz ht
  rw [hz, ht]
  congr 1
  ext i
  simp only [coulombPermute_apply, Equiv.symm_apply_apply]

def poleBranchComplexConj (N : ℕ) (β : ℝ) :
    Lp ℂ 2 (coulombMeasure N β) →L[ℝ] Lp ℂ 2 (coulombMeasure N β) :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 (coulombMeasure N β)

theorem poleBranchComplexConj_coe {N : ℕ} {β : ℝ} (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexConj N β v =ᵐ[coulombMeasure N β] fun z => star (v z) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL v

theorem poleBranchComplexConj_involutive (N : ℕ) (β : ℝ) :
    Function.Involutive (poleBranchComplexConj N β) := by
  intro v
  apply Lp.ext
  filter_upwards [poleBranchComplexConj_coe (poleBranchComplexConj N β v), poleBranchComplexConj_coe v]
    with z hz hv
  rw [hz, hv, star_star]

theorem poleBranchComplexConj_norm {N : ℕ} {β : ℝ} (v : Lp ℂ 2 (coulombMeasure N β)) :
    ‖poleBranchComplexConj N β v‖ = ‖v‖ := by
  have hb (w : Lp ℂ 2 (coulombMeasure N β)) : ‖poleBranchComplexConj N β w‖ ≤ ‖w‖ := by
    calc
      _ ≤ ‖Complex.conjCLE.toContinuousLinearMap‖ * ‖w‖ :=
        Complex.conjCLE.toContinuousLinearMap.norm_compLp_le w
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right Complex.conjLIE.toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg w)
      _ = _ := one_mul _
  apply le_antisymm (hb v)
  simpa only [poleBranchComplexConj_involutive N β v] using hb (poleBranchComplexConj N β v)

theorem poleBranchComplexConj_permute {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexPermute N hβ σ (poleBranchComplexConj N β v) =
      poleBranchComplexConj N β (poleBranchComplexPermute N hβ σ v) := by
  have ht := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae (poleBranchComplexConj_coe v)
  apply Lp.ext
  filter_upwards [poleBranchComplexPermute_coe hβ σ (poleBranchComplexConj N β v), ht,
    poleBranchComplexConj_coe (poleBranchComplexPermute N hβ σ v), poleBranchComplexPermute_coe hβ σ v]
    with z hpc hc hcp hp
  rw [hpc, hc, hcp, hp]

def poleBranchComplexOne (N : ℕ) {β : ℝ} (hβ : 0 < β) : Lp ℂ 2 (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact (memLp_const (1 : ℂ)).toLp (fun _ => 1)

theorem poleBranchComplexOne_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchComplexOne N hβ =ᵐ[coulombMeasure N β] fun _ => (1 : ℂ) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact MemLp.coeFn_toLp (memLp_const (1 : ℂ))

end RepulsiveCoulomb
