import LeanResearch.RepulsiveCoulomb.SectorVariation
import Mathlib.Topology.Homeomorph.Defs

/-! SOURCE-ONLY, UNCOMPILED. An actual closed-sector piece homeomorphism,
including the apex and both seams. Forward and inverse continuity are proved
from the sharp pairwise estimates. Boundary arclength is preserved separately
on each ray; no cross-ray distance preservation is asserted. -/
noncomputable section
open Set
open scoped NNReal ENNReal
namespace RepulsiveCoulomb

/-- The source and target are literal closed Euclidean sector subtypes. -/
def closedSectorContractionEquiv {c β : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    closedEuclideanSector β ≃ closedEuclideanSector (c * β) := by
  let f : closedEuclideanSector β → closedEuclideanSector (c * β) :=
    fun z ↦ ⟨sectorAngularMap c z,
      sectorAngularMap_mapsTo hc.le hc1 hβπ z.property⟩
  apply Equiv.ofBijective f
  have hb := sectorAngularMap_bijOn hc hc1 hβ hβπ
  constructor
  · intro x z hxz
    apply Subtype.ext
    exact hb.injOn x.property z.property (congrArg Subtype.val hxz)
  · intro w
    obtain ⟨z, hz, hzw⟩ := hb.surjOn w.property
    exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩

@[simp] theorem closedSectorContractionEquiv_apply {c β : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (z : closedEuclideanSector β) :
    (closedSectorContractionEquiv hc hc1 hβ hβπ z : ℂ) = sectorAngularMap c z := rfl

theorem closedSectorContractionEquiv_dist_bounds {c β : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (x z : closedEuclideanSector β) :
    c * dist x z ≤ dist (closedSectorContractionEquiv hc hc1 hβ hβπ x)
        (closedSectorContractionEquiv hc hc1 hβ hβπ z) ∧
      dist (closedSectorContractionEquiv hc hc1 hβ hβπ x)
        (closedSectorContractionEquiv hc hc1 hβ hβπ z) ≤ dist x z := by
  simpa only [Subtype.dist_eq, dist_eq_norm, closedSectorContractionEquiv_apply] using
    sectorAngularMap_dist_bounds hc.le hc1 hβπ x.property z.property

def closedSectorContractionHomeomorph {c β : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    closedEuclideanSector β ≃ₜ closedEuclideanSector (c * β) := by
  let e := closedSectorContractionEquiv hc hc1 hβ hβπ
  have hf : LipschitzWith 1 e := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    simpa using (closedSectorContractionEquiv_dist_bounds hc hc1 hβ hβπ x z).2
  have hg : LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ e.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    have h := (closedSectorContractionEquiv_dist_bounds hc hc1 hβ hβπ
      (e.symm x) (e.symm z)).1
    change c * dist (e.symm x) (e.symm z) ≤ dist (e (e.symm x)) (e (e.symm z)) at h
    rw [e.apply_symm_apply, e.apply_symm_apply] at h
    change dist (e.symm x) (e.symm z) ≤ c⁻¹ * dist x z
    simpa only [div_eq_inv_mul] using (le_div_iff₀ hc).mpr (by simpa [mul_comm] using h)
  exact { e with continuous_toFun := hf.continuous, continuous_invFun := hg.continuous }

/-- Every rectifiable path inside the closed piece, even one with infinitely
many seam visits, has the sharp two-sided length comparison. -/
theorem closedSectorContractionHomeomorph_variation_bounds
    {A : Type*} [LinearOrder A] {c β : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (γ : A → closedEuclideanSector β) (s : Set A) :
    ENNReal.ofReal c * eVariationOn γ s ≤
        eVariationOn (closedSectorContractionHomeomorph hc hc1 hβ hβπ ∘ γ) s ∧
      eVariationOn (closedSectorContractionHomeomorph hc hc1 hβ hβπ ∘ γ) s ≤
        eVariationOn γ s := by
  let e := closedSectorContractionHomeomorph hc hc1 hβ hβπ
  have hbound (x z : closedEuclideanSector β) :
      c * dist x z ≤ dist (e x) (e z) ∧ dist (e x) (e z) ≤ dist x z :=
    closedSectorContractionEquiv_dist_bounds hc hc1 hβ hβπ x z
  constructor
  · apply eVariationOn_lower_of_edist_lower (t := univ) _ (mapsTo_univ γ s)
    intro x _ z _
    have h := ENNReal.ofReal_le_ofReal (hbound x z).1
    simpa only [edist_dist, ENNReal.ofReal_mul hc.le] using h
  · have hlip : LipschitzWith 1 e := by
      apply LipschitzWith.of_dist_le_mul
      intro x z
      simpa only [NNReal.coe_one, one_mul] using (hbound x z).2
    simpa only [ENNReal.coe_one, one_mul] using
      hlip.lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ γ s)

end RepulsiveCoulomb
