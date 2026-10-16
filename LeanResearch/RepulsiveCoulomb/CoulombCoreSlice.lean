module

public import LeanResearch.RepulsiveCoulomb.CoulombSliceGeometry

@[expose] public section

/-! Actual full collision-free test functions restrict to the prescribed
point-punctured smooth core, with the exact physical partial gradient. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulomb_core_slice_tsupport {N : ℕ} (a : Fin N → ℝ)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤) (y : CoulombConfig N) :
    tsupport (fun w : ℂ => φ (coulombInsertZero w y)) ⊆ pointDomain a (fun j => y j) := by
  intro w hw
  have hs := tsupport_comp_subset_preimage (φ : CoulombConfig (N + 1) → ℝ)
    (coulombInsertZero_contDiff y).continuous hw
  have hz := (coulombVandermonde_ne_zero_iff (coulombInsertZero w y)).mp (φ.tsupport_subset hs)
  change w ∉ pointPunctures a (fun j => y j)
  rintro ⟨j, hj, he⟩
  exact (hz 0 j.succ (Fin.succ_ne_zero j).symm) (by simpa only [coulombInsertZero_zero, coulombInsertZero_succ] using he)

def coulombCoreSliceZero {N : ℕ} (a : Fin N → ℝ)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤) (y : CoulombConfig N) :
    TestFunction (pointDomain a (fun j => y j)) ℝ ⊤ :=
  ⟨fun w => φ (coulombInsertZero w y),
    φ.contDiff.comp (coulombInsertZero_contDiff y),
    φ.hasCompactSupport.comp_isClosedEmbedding (coulombInsertZero_isometry y).isClosedEmbedding,
    coulomb_core_slice_tsupport a φ y⟩

theorem coulombCoreSliceZero_apply {N : ℕ} (a : Fin N → ℝ)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤) (y : CoulombConfig N) (w : ℂ) :
    coulombCoreSliceZero a φ y w = φ (coulombInsertZero w y) := rfl

theorem coulombCoreSliceZero_gradient {N : ℕ} (a : Fin N → ℝ)
    (φ : TestFunction (coulombDomain (N + 1)) ℝ ⊤) (y : CoulombConfig N) (w : ℂ) :
    gradient (coulombCoreSliceZero a φ y : ℂ → ℝ) w =
      gradient (φ : CoulombConfig (N + 1) → ℝ) (coulombInsertZero w y) 0 :=
  coulomb_first_slice_gradient y w (φ.contDiff.differentiable (by simp) _)

end RepulsiveCoulomb

