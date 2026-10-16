module

public import LeanResearch.RepulsiveCoulomb.PlanarProperRayCompactification
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

@[expose] public section

/-! Remove the common marked infinity of an actual compactification extension.
The inverse pole is restored by properness of the ambient homeomorphism; the
formula is continuous there despite each individual inversion being singular. -/
noncomputable section
open Set Topology Filter
namespace RepulsiveCoulomb

def planarInversionConjugate (F : ℂ ≃ₜ ℂ) (p q z : ℂ) : ℂ :=
  q + (F (planarInversion p z))⁻¹

@[simp] theorem planarInversionConjugate_pole (F : ℂ ≃ₜ ℂ) (hF : F 0 = 0)
    (p q : ℂ) : planarInversionConjugate F p q p = q := by
  simp [planarInversionConjugate, planarInversion, hF]

theorem planarInversion_tendsto_pole (p : ℂ) :
    Tendsto (planarInversion p) (𝓝[≠] p) (cocompact ℂ) := by
  have ht : Tendsto (fun z : ℂ ↦ z - p) (𝓝[≠] p) (𝓝[≠] 0) := by
    have h := ((Homeomorph.subRight p).map_punctured_nhds_eq p).le
    change Filter.map (fun z : ℂ ↦ z - p) (𝓝[≠] p) ≤ 𝓝[≠] (0 : ℂ)
    simpa only [Homeomorph.coe_subRight, sub_self] using h
  have hi := (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp ht
  change Tendsto (fun z : ℂ ↦ (z - p)⁻¹) (𝓝[≠] p) (cocompact ℂ)
  simpa only [Metric.cobounded_eq_cocompact, Function.comp_def] using hi

theorem planarInversionConjugate_continuous (F : ℂ ≃ₜ ℂ) (hF : F 0 = 0)
    (p q : ℂ) : Continuous (planarInversionConjugate F p q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = p
  · subst z
    apply continuousAt_iff_punctured_nhds.mpr
    have hproper : Tendsto F (cocompact ℂ) (cocompact ℂ) := F.map_cocompact.le
    have hi : Tendsto (fun w : ℂ ↦ w⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_cobounded (α := ℂ))
    have h := (tendsto_const_nhds (x := q)).add
      (hi.comp (hproper.comp (planarInversion_tendsto_pole p)))
    rw [planarInversionConjugate_pole F hF]
    change Tendsto (fun z : ℂ ↦ q + (F (planarInversion p z))⁻¹) (𝓝[≠] p) (𝓝 q)
    simpa only [Function.comp_def, add_zero] using h
  · have hI : ContinuousAt (planarInversion p) z :=
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hz)
    have hne : F (planarInversion p z) ≠ 0 := by
      intro he
      exact planarInversion_ne_zero hz (F.injective (he.trans hF.symm))
    exact continuousAt_const.add ((F.continuous.continuousAt.comp hI).inv₀ hne)

/-- A genuine self-homeomorphism of the uncompactified planes. The formula is
valid at the restored pole because inverses in a field have value zero at zero. -/
def planarInversionConjugateHomeomorph (F : ℂ ≃ₜ ℂ) (hF : F 0 = 0)
    (p q : ℂ) : ℂ ≃ₜ ℂ where
  toFun := planarInversionConjugate F p q
  invFun := planarInversionConjugate F.symm q p
  left_inv z := by simp [planarInversionConjugate, planarInversion]
  right_inv z := by simp [planarInversionConjugate, planarInversion]
  continuous_toFun := planarInversionConjugate_continuous F hF p q
  continuous_invFun := planarInversionConjugate_continuous F.symm
    (by apply F.injective; rw [F.apply_symm_apply, hF]) q p

@[simp] theorem planarInversionConjugateHomeomorph_apply
    (F : ℂ ≃ₜ ℂ) (hF : F 0 = 0) (p q z : ℂ) :
    planarInversionConjugateHomeomorph F hF p q z =
      q + (F (planarInversion p z))⁻¹ := rfl

end RepulsiveCoulomb
