import LeanResearch.RepulsiveCoulomb.CoulombOptimalPoincare
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring

/-! RECORDS-ONLY UNCOMPILED. The manuscript's exact C_sym, using the actual
optimal full-domain Poincare coefficient from CoulombOptimalPoincare. The
finite inner maximum is omitted when empty. No admissible witness is renamed
as an optimal constant, and no symmetric dbar estimate is assumed here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb

def poleBranchExceptionalParticleCounts (β : ℝ) : Finset ℕ :=
  Finset.Icc 2 ⌊β / 2⌋₊

theorem poleBranchExceptionalParticleCounts_mem {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    N ∈ poleBranchExceptionalParticleCounts β ↔ 2 ≤ N ∧ (N : ℝ) ≤ β / 2 := by
  rw [poleBranchExceptionalParticleCounts, Finset.mem_Icc,
    Nat.le_floor_iff (by positivity : 0 ≤ β / 2)]

theorem poleBranchExceptionalParticleCounts_mono {β γ : ℝ} (h : β ≤ γ) :
    poleBranchExceptionalParticleCounts β ⊆ poleBranchExceptionalParticleCounts γ := by
  intro N hN
  obtain ⟨h2, hfloor⟩ := Finset.mem_Icc.mp hN
  exact Finset.mem_Icc.mpr ⟨h2, hfloor.trans (Nat.floor_mono (by linarith : β / 2 ≤ γ / 2))⟩

theorem poleBranchExceptionalParticleCounts_empty {β : ℝ} (hβ : 0 ≤ β) (h4 : β < 4) :
    poleBranchExceptionalParticleCounts β = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro N hN
  obtain ⟨h2, hsmall⟩ := (poleBranchExceptionalParticleCounts_mem hβ N).mp hN
  have h2R : (2 : ℝ) ≤ N := by exact_mod_cast h2
  linarith

def poleBranchSymmetricPoincareConstant {β : ℝ} (hβ : 0 < β) : ℝ :=
  if hs : (poleBranchExceptionalParticleCounts β).Nonempty then
    max (1 / β) ((poleBranchExceptionalParticleCounts β).sup' hs
      (fun N => coulombOptimalPoincare N hβ))
  else 1 / β

theorem poleBranchSymmetricPoincareConstant_eq_max {β : ℝ} (hβ : 0 < β)
    (hs : (poleBranchExceptionalParticleCounts β).Nonempty) :
    poleBranchSymmetricPoincareConstant hβ =
      max (1 / β) ((poleBranchExceptionalParticleCounts β).sup' hs
        (fun N => coulombOptimalPoincare N hβ)) := by
  simp only [poleBranchSymmetricPoincareConstant, dif_pos hs]

theorem poleBranchSymmetricPoincareConstant_eq_inverse {β : ℝ} (hβ : 0 < β)
    (hs : ¬(poleBranchExceptionalParticleCounts β).Nonempty) :
    poleBranchSymmetricPoincareConstant hβ = 1 / β := by
  simp only [poleBranchSymmetricPoincareConstant, dif_neg hs]

theorem poleBranchSymmetricPoincareConstant_eq_inverse_of_lt_four {β : ℝ}
    (hβ : 0 < β) (h4 : β < 4) : poleBranchSymmetricPoincareConstant hβ = 1 / β := by
  apply poleBranchSymmetricPoincareConstant_eq_inverse hβ
  rw [poleBranchExceptionalParticleCounts_empty hβ.le h4]
  exact Finset.not_nonempty_empty

theorem poleBranchSymmetricPoincareConstant_one_div_le {β : ℝ} (hβ : 0 < β) :
    1 / β ≤ poleBranchSymmetricPoincareConstant hβ := by
  unfold poleBranchSymmetricPoincareConstant
  split
  · exact le_max_left _ _
  · exact le_rfl

theorem poleBranchSymmetricPoincareConstant_pos {β : ℝ} (hβ : 0 < β) :
    0 < poleBranchSymmetricPoincareConstant hβ :=
  (one_div_pos.mpr hβ).trans_le (poleBranchSymmetricPoincareConstant_one_div_le hβ)

theorem poleBranchSymmetricPoincareConstant_optimal_le {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : N ∈ poleBranchExceptionalParticleCounts β) :
    coulombOptimalPoincare N hβ ≤ poleBranchSymmetricPoincareConstant hβ := by
  have hs : (poleBranchExceptionalParticleCounts β).Nonempty := ⟨N, hN⟩
  rw [poleBranchSymmetricPoincareConstant_eq_max hβ hs]
  exact (Finset.le_sup' (fun M => coulombOptimalPoincare M hβ) hN).trans (le_max_right _ _)

theorem poleBranchSymmetricPoincareConstant_le {β C : ℝ} (hβ : 0 < β)
    (hbase : 1 / β ≤ C)
    (hfinite : ∀ N ∈ poleBranchExceptionalParticleCounts β, coulombOptimalPoincare N hβ ≤ C) :
    poleBranchSymmetricPoincareConstant hβ ≤ C := by
  unfold poleBranchSymmetricPoincareConstant
  split
  · exact max_le hbase (Finset.sup'_le _ _ hfinite)
  · exact hbase

def poleBranchSymmetricPoincareValues {β : ℝ} (hβ : 0 < β) : Set ℝ :=
  insert (1 / β) ((fun N => coulombOptimalPoincare N hβ) ''
    (poleBranchExceptionalParticleCounts β : Set ℕ))

theorem poleBranchSymmetricPoincareConstant_isLUB {β : ℝ} (hβ : 0 < β) :
    IsLUB (poleBranchSymmetricPoincareValues hβ) (poleBranchSymmetricPoincareConstant hβ) := by
  constructor
  · intro C hC
    rcases hC with rfl | ⟨N, hN, rfl⟩
    · exact poleBranchSymmetricPoincareConstant_one_div_le hβ
    · exact poleBranchSymmetricPoincareConstant_optimal_le hβ N hN
  · intro C hC
    apply poleBranchSymmetricPoincareConstant_le hβ (hC (Or.inl rfl))
    intro N hN
    exact hC (Or.inr ⟨N, hN, rfl⟩)

theorem poleBranchSymmetricPoincareValues_bddAbove {β : ℝ} (hβ : 0 < β) :
    BddAbove (poleBranchSymmetricPoincareValues hβ) :=
  ⟨poleBranchSymmetricPoincareConstant hβ, (poleBranchSymmetricPoincareConstant_isLUB hβ).1⟩

end RepulsiveCoulomb
