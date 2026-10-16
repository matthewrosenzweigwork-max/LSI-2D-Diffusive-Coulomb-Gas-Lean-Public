import LeanResearch.RepulsiveCoulomb.CoulombOneSiteFactorization

/-! Actual measure-preserving first-coordinate splitting of Euclidean configurations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombSplitZero (N : ℕ) : CoulombConfig (N + 1) ≃ᵐ ℂ × CoulombConfig N :=
  ((MeasurableEquiv.toLp 2 (Fin (N + 1) → ℂ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0)).trans
    ((MeasurableEquiv.refl ℂ).prodCongr (MeasurableEquiv.toLp 2 (Fin N → ℂ)))

theorem coulombSplitZero_measurePreserving (N : ℕ) : MeasurePreserving (coulombSplitZero N) := by
  have h0 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (N + 1) → ℂ)).symm :=
    coulomb_coordinates_volume_preserving (N + 1)
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0
  have ho : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm
      (volume : Measure (CoulombConfig N)) (volume : Measure (Fin N → ℂ)) :=
    coulomb_coordinates_volume_preserving N
  have ht : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin N → ℂ)) := ho.symm
  have h2 : MeasurePreserving ((MeasurableEquiv.refl ℂ).prodCongr (MeasurableEquiv.toLp 2 (Fin N → ℂ))) :=
    (MeasurePreserving.id (volume : Measure ℂ)).prod ht
  exact (h0.trans h1).trans h2

theorem coulombSplitZero_insert {N : ℕ} (w : ℂ) (y : CoulombConfig N) :
    coulombSplitZero N (coulombInsertZero w y) = (w, y) := by
  apply Prod.ext
  · rfl
  · ext j
    rfl

theorem coulombSplitZero_symm_apply {N : ℕ} (w : ℂ) (y : CoulombConfig N) :
    (coulombSplitZero N).symm (w, y) = coulombInsertZero w y := by
  apply (coulombSplitZero N).injective
  rw [MeasurableEquiv.apply_symm_apply, coulombSplitZero_insert]

theorem coulombInsertZero_measurable (N : ℕ) :
    Measurable (fun p : ℂ × CoulombConfig N => coulombInsertZero p.1 p.2) := by
  have he : (fun p : ℂ × CoulombConfig N => coulombInsertZero p.1 p.2) = (coulombSplitZero N).symm := by
    funext p
    exact (coulombSplitZero_symm_apply p.1 p.2).symm
  rw [he]
  exact (coulombSplitZero N).symm.measurable

end RepulsiveCoulomb
