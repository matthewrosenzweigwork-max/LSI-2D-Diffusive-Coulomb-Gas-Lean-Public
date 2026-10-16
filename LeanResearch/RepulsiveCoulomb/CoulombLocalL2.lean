module

public import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal

@[expose] public section

/-! Actual local weighted-to-Lebesgue L2 restriction for the particle model.
No Haar instance is imposed on the Gibbs measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulombMeasure_volume_restrict_le {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K s : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) (hs : s ⊆ K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ volume.restrict s ≤ C • coulombMeasure N β := by
  obtain ⟨c, D, hc, hD, hlo, hhi⟩ := coulombMeasure_restrict_comparison hβ hK havoid
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  refine ⟨(ENNReal.ofReal c)⁻¹, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  have hr : volume.restrict K ≤ (ENNReal.ofReal c)⁻¹ • (coulombMeasure N β).restrict K := by
    have h := smul_le_smul_left (ENNReal.ofReal c)⁻¹ hlo
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using h
  exact (Measure.restrict_mono_set _ hs).trans (hr.trans (smul_le_smul_left _ Measure.restrict_le_self))

def coulombL2RestrictToVolume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K s : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) (hs : s ⊆ K)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 (coulombMeasure N β) →L[ℝ] Lp F 2 (volume.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul
    (coulombMeasure_volume_restrict_le hβ hK havoid hs).choose_spec.1
    (coulombMeasure_volume_restrict_le hβ hK havoid hs).choose_spec.2

theorem coulombL2RestrictToVolume_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K s : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) (hs : s ⊆ K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Lp F 2 (coulombMeasure N β)) :
    coulombL2RestrictToVolume hβ hK havoid hs F f =ᵐ[volume.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

end RepulsiveCoulomb
