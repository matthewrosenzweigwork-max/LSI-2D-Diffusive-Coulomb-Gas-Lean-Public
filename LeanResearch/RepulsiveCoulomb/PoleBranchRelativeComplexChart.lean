import LeanResearch.RepulsiveCoulomb.CoulombRelativeKernel
import LeanResearch.RepulsiveCoulomb.CoulombPermutation

/-! Complex-linearity of the existing exact, volume-preserving relative chart. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

def poleBranchRelativeInsertLinear (N : ℕ) :
    ((ℂ × CoulombConfig N) × ℂ) →ₗ[ℂ] CoulombConfig (N + 2) where
  toFun p := coulombRelativeInsert p.1.1 p.2 p.1.2
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [coulombRelativeInsert_zero, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
      module
    · simp only [coulombRelativeInsert_one, Prod.fst_add, Prod.snd_add, PiLp.add_apply]
      module
    · rfl
  map_smul' a p := by
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · change (Real.sqrt 2)⁻¹ • (a • p.1.1 + a • p.2) =
        a • ((Real.sqrt 2)⁻¹ • (p.1.1 + p.2))
      rw [← smul_add]
      exact smul_comm (Real.sqrt 2)⁻¹ a (p.1.1 + p.2)
    · change (Real.sqrt 2)⁻¹ • (a • p.1.1 - a • p.2) =
        a • ((Real.sqrt 2)⁻¹ • (p.1.1 - p.2))
      rw [← smul_sub]
      exact smul_comm (Real.sqrt 2)⁻¹ a (p.1.1 - p.2)
    · rfl

def poleBranchRelativeInsertEquiv (N : ℕ) :
    ((ℂ × CoulombConfig N) × ℂ) ≃L[ℂ] CoulombConfig (N + 2) :=
  (LinearEquiv.ofBijective (poleBranchRelativeInsertLinear N) (by
    have he : (poleBranchRelativeInsertLinear N : ((ℂ × CoulombConfig N) × ℂ) → CoulombConfig (N + 2)) =
        (coulombRelativeFrozenFirst N).symm := by
      funext p
      exact (coulombRelativeFrozenFirst_symm_apply p.1 p.2).symm
    rw [he]
    exact (coulombRelativeFrozenFirst N).symm.bijective)).toContinuousLinearEquiv

theorem poleBranchRelativeInsertEquiv_apply (N : ℕ) (p : (ℂ × CoulombConfig N) × ℂ) :
    poleBranchRelativeInsertEquiv N p = coulombRelativeInsert p.1.1 p.2 p.1.2 := rfl

theorem poleBranchRelativeInsertEquiv_measurePreserving (N : ℕ) :
    MeasurePreserving (poleBranchRelativeInsertEquiv N)
      (volume : Measure ((ℂ × CoulombConfig N) × ℂ)) volume := by
  have he : (poleBranchRelativeInsertEquiv N : ((ℂ × CoulombConfig N) × ℂ) → CoulombConfig (N + 2)) =
      (coulombRelativeFrozenFirst N).symm := by
    funext p
    exact (coulombRelativeFrozenFirst_symm_apply p.1 p.2).symm
  rw [he]
  exact (coulombRelativeFrozenFirst_measurePreserving N).symm

theorem poleBranch_coulombPermute_differentiable {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Differentiable ℂ (coulombPermute σ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm).differentiable

end RepulsiveCoulomb
