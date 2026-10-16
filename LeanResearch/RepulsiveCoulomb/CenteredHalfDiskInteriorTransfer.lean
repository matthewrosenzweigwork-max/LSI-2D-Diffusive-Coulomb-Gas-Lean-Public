module

public import LeanResearch.RepulsiveCoulomb.PointPassingEdgeOccupancy

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Strict halfdisk source points really lie in the
interior of the original sector source. This bridges directed open-arc lifting
to the actual full sector's open image, including a passing-edge chart. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem centeredHalfDiskInclusion_mem_interior {K : Set ℂ} {R : ℝ}
    (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im))
    (w : flatLinkSectorDisk Real.pi R) (hwR : ‖w.1‖ < R) (hwim : 0 < w.1.im) :
    (centeredHalfDiskInclusion e hK w : ℂ) ∈ interior K := by
  let V : Set ℂ := {v | ‖v‖ < R ∧ 0 < v.im}
  have hV : IsOpen V := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  let U : Set ℂ := e.symm ⁻¹' V
  have hU : IsOpen U := hV.preimage e.symm.continuous
  have hUK : U ⊆ K := by
    intro z hz
    have hz' : ‖e.symm z‖ < R ∧ 0 < (e.symm z).im := hz
    have hmem := (hK (e.symm z) hz'.1.le).mpr hz'.2.le
    simpa only [e.apply_symm_apply] using hmem
  have hwU : (centeredHalfDiskInclusion e hK w : ℂ) ∈ U := by
    change ‖e.symm (e w.1)‖ < R ∧ 0 < (e.symm (e w.1)).im
    simpa only [e.symm_apply_apply] using And.intro hwR hwim
  exact interior_mono hUK (by simpa only [hU.interior_eq] using hwU)

theorem pointCenteredHalfDiskMap_mem_openImage {K : Set ℂ} {R : ℝ}
    (f : K → ℂ) (e : ℂ ≃ᵢ ℂ)
    (hK : ∀ w : ℂ, ‖w‖ ≤ R → (e w ∈ K ↔ 0 ≤ w.im))
    (w : flatLinkSectorDisk Real.pi R) (hwR : ‖w.1‖ < R) (hwim : 0 < w.1.im) :
    pointCenteredHalfDiskMap f e hK w ∈ f '' {x : K | x.1 ∈ interior K} :=
  ⟨centeredHalfDiskInclusion e hK w,
    centeredHalfDiskInclusion_mem_interior e hK w hwR hwim, rfl⟩

end RepulsiveCoulomb
