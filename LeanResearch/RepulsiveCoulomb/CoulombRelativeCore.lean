module

public import LeanResearch.RepulsiveCoulomb.CoulombRelativeRoots

@[expose] public section

/-! Collision-free smooth cores restrict to the literal relative punctured core. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulomb_relative_core_tsupport {N : ℕ} (a : Fin (N + N + 1) → ℝ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) (c : ℂ) (y : CoulombConfig N) :
    tsupport (fun u => φ (coulombRelativeInsert c u y)) ⊆ pointDomain a (coulombRelativeRoots c y) := by
  intro u hu
  have hs := tsupport_comp_subset_preimage (φ : CoulombConfig (N + 2) → ℝ)
    (coulombRelativeInsert_contDiff c y).continuous hu
  have hz := (coulombVandermonde_ne_zero_iff (coulombRelativeInsert c u y)).mp (φ.tsupport_subset hs)
  change u ∉ pointPunctures a (coulombRelativeRoots c y)
  rintro ⟨k, hk, he⟩
  revert he
  refine Fin.cases ?_ (fun l => ?_) k
  · intro he
    have hne := hz 0 (Fin.succ 0) (Fin.succ_ne_zero (0 : Fin (N + 1))).symm
    apply hne
    apply sub_eq_zero.mp
    rw [coulombRelative_pair_difference, he, coulombRelativeRoots_zero, smul_zero]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    · intro he
      rw [coulombRelativeRoots_left] at he
      have hne := hz 0 j.succ.succ (Fin.succ_ne_zero j.succ).symm
      apply hne
      apply sub_eq_zero.mp
      rw [coulombRelative_left_difference, he, sub_self, smul_zero]
    · intro he
      rw [coulombRelativeRoots_right] at he
      have hne := hz (Fin.succ 0) j.succ.succ (by
        intro h
        exact (Fin.succ_ne_zero j).symm (Fin.succ_inj.mp h))
      apply hne
      apply sub_eq_zero.mp
      rw [coulombRelative_right_difference, he, neg_add_cancel, smul_zero, neg_zero]

def coulombRelativeCore {N : ℕ} (a : Fin (N + N + 1) → ℝ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) (c : ℂ) (y : CoulombConfig N) :
    TestFunction (pointDomain a (coulombRelativeRoots c y)) ℝ ⊤ :=
  ⟨fun u => φ (coulombRelativeInsert c u y),
    φ.contDiff.comp (coulombRelativeInsert_contDiff c y),
    φ.hasCompactSupport.comp_isClosedEmbedding (coulombRelativeInsert_isometry c y).isClosedEmbedding,
    coulomb_relative_core_tsupport a φ c y⟩

theorem coulombRelativeCore_apply {N : ℕ} (a : Fin (N + N + 1) → ℝ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) (c u : ℂ) (y : CoulombConfig N) :
    coulombRelativeCore a φ c y u = φ (coulombRelativeInsert c u y) := rfl

theorem coulombRelativeCore_gradient {N : ℕ} (a : Fin (N + N + 1) → ℝ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) (c u : ℂ) (y : CoulombConfig N) :
    gradient (coulombRelativeCore a φ c y : ℂ → ℝ) u =
      (Real.sqrt 2)⁻¹ • (gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)) :=
  coulomb_relative_slice_gradient c u y (φ.contDiff.differentiable (by simp) _)

end RepulsiveCoulomb

