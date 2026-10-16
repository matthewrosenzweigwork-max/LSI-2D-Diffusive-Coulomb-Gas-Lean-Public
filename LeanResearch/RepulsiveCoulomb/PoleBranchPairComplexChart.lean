import LeanResearch.RepulsiveCoulomb.PoleBranchRelativeComplexChart
import LeanResearch.RepulsiveCoulomb.CoulombAllPairsSwap

/-! The existing relative chart transported to any actual pair of labels,
with its exact collision coordinate and transposition reflection. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

def poleBranchPermuteEquiv {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    CoulombConfig N ≃L[ℂ] CoulombConfig N :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ.symm).toContinuousLinearEquiv

theorem poleBranchPermuteEquiv_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N) :
    poleBranchPermuteEquiv σ z = coulombPermute σ z := rfl

def poleBranchPairChart {N : ℕ} (σ : Equiv.Perm (Fin (N + 2))) :
    ((ℂ × CoulombConfig N) × ℂ) ≃L[ℂ] CoulombConfig (N + 2) :=
  (poleBranchRelativeInsertEquiv N).trans (poleBranchPermuteEquiv σ.symm)

theorem poleBranchPairChart_apply {N : ℕ} (σ : Equiv.Perm (Fin (N + 2)))
    (p : (ℂ × CoulombConfig N) × ℂ) :
    poleBranchPairChart σ p = coulombPermute σ.symm (coulombRelativeInsert p.1.1 p.2 p.1.2) := rfl

theorem poleBranchPairChart_measurePreserving {N : ℕ} (σ : Equiv.Perm (Fin (N + 2))) :
    MeasurePreserving (poleBranchPairChart σ)
      (volume : Measure ((ℂ × CoulombConfig N) × ℂ)) volume :=
  (coulombPermute_volume_preserving σ.symm).comp (poleBranchRelativeInsertEquiv_measurePreserving N)

theorem poleBranchPairChart_difference {N : ℕ} (σ : Equiv.Perm (Fin (N + 2)))
    (i j : Fin (N + 2)) (hσ0 : σ 0 = i) (hσ1 : σ (Fin.succ 0) = j)
    (p : (ℂ × CoulombConfig N) × ℂ) :
    poleBranchPairChart σ p i - poleBranchPairChart σ p j = Real.sqrt 2 • p.2 := by
  rw [poleBranchPairChart_apply, coulombPermute_apply, coulombPermute_apply,
    ← hσ0, ← hσ1, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact coulombRelative_pair_difference p.1.1 p.2 p.1.2

theorem poleBranchPairChart_reflection {N : ℕ} (σ : Equiv.Perm (Fin (N + 2)))
    (i j : Fin (N + 2)) (hσ0 : σ 0 = i) (hσ1 : σ (Fin.succ 0) = j)
    (p : ℂ × CoulombConfig N) (u : ℂ) :
    poleBranchPairChart σ (p, -u) = coulombPermute (Equiv.swap i j) (poleBranchPairChart σ (p, u)) := by
  rw [poleBranchPairChart_apply, ← coulombSwapFirst_relative, coulombSwapFirst_eq_permute,
    coulombPermute_swap_conjugacy]
  simp only [Equiv.symm_symm, hσ0, hσ1, poleBranchPairChart_apply]

theorem poleBranchPairChart_inverse_normal_zero {N : ℕ} (σ : Equiv.Perm (Fin (N + 2)))
    (i j : Fin (N + 2)) (hσ0 : σ 0 = i) (hσ1 : σ (Fin.succ 0) = j)
    (z : CoulombConfig (N + 2)) (hz : z i = z j) :
    ((poleBranchPairChart σ).symm z).2 = 0 := by
  have h := poleBranchPairChart_difference σ i j hσ0 hσ1 ((poleBranchPairChart σ).symm z)
  rw [(poleBranchPairChart σ).apply_symm_apply, hz, sub_self] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (Real.sqrt_pos.mpr (by norm_num)).ne'

end RepulsiveCoulomb
