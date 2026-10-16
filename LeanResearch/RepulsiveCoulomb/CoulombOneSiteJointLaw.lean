import LeanResearch.RepulsiveCoulomb.CoulombOneSiteKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Equality of the actual joint law with marginal times the conditional
kernel, and a signed tower with genuine integrability hypotheses. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal ProbabilityTheory
namespace RepulsiveCoulomb

def coulombFrozenFirst (N : ℕ) : CoulombConfig (N + 1) ≃ᵐ CoulombConfig N × ℂ :=
  (coulombSplitZero N).trans (MeasurableEquiv.prodComm : ℂ × CoulombConfig N ≃ᵐ CoulombConfig N × ℂ)

theorem coulombFrozenFirst_insert {N : ℕ} (w : ℂ) (y : CoulombConfig N) :
    coulombFrozenFirst N (coulombInsertZero w y) = (y, w) := by
  change (coulombSplitZero N (coulombInsertZero w y)).swap = (y, w)
  rw [coulombSplitZero_insert]
  rfl

theorem coulombFrozenFirst_symm_apply {N : ℕ} (y : CoulombConfig N) (w : ℂ) :
    (coulombFrozenFirst N).symm (y, w) = coulombInsertZero w y := by
  apply (coulombFrozenFirst N).injective
  rw [MeasurableEquiv.apply_symm_apply, coulombFrozenFirst_insert]

theorem coulomb_one_site_joint_law {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Measure.map (coulombFrozenFirst N) (coulombMeasure (N + 1) β) =
      coulombOneSiteMarginal N β ⊗ₘ coulombOneSiteKernel N β hβ := by
  let _ := coulombOneSiteMarginal_isProbability (N := N) hβ
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (coulombFrozenFirst N).measurable, Measure.lintegral_compProd hF]
  have h := coulomb_one_site_kernel_tower hβ (hF.comp (coulombFrozenFirst N).measurable)
  simpa only [Function.comp_apply, coulombFrozenFirst_insert] using h

theorem coulombFrozenFirst_measurePreserving {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    MeasurePreserving (coulombFrozenFirst N) (coulombMeasure (N + 1) β)
      (coulombOneSiteMarginal N β ⊗ₘ coulombOneSiteKernel N β hβ) :=
  ⟨(coulombFrozenFirst N).measurable, coulomb_one_site_joint_law hβ⟩

theorem coulomb_one_site_slice_integrability {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 1) → ℝ} (hF : Integrable F (coulombMeasure (N + 1) β)) :
    (∀ᵐ y ∂coulombOneSiteMarginal N β,
      Integrable (fun w => F (coulombInsertZero w y)) (coulombOneSiteKernel N β hβ y)) ∧
      Integrable (fun y => ∫ w, |F (coulombInsertZero w y)| ∂coulombOneSiteKernel N β hβ y)
        (coulombOneSiteMarginal N β) := by
  let _ := coulombOneSiteMarginal_isProbability (N := N) hβ
  have hi := (coulombFrozenFirst_measurePreserving (N := N) hβ).symm.integrable_comp_of_integrable hF
  have h := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  simpa only [Function.comp_apply, Function.uncurry_apply_pair, coulombFrozenFirst_symm_apply, Real.norm_eq_abs] using h

theorem coulomb_one_site_integral_tower {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 1) → ℝ} (hF : Integrable F (coulombMeasure (N + 1) β)) :
    (∫ z, F z ∂coulombMeasure (N + 1) β) =
      ∫ y : CoulombConfig N, (∫ w : ℂ, F (coulombInsertZero w y) ∂coulombOneSiteKernel N β hβ y)
        ∂coulombOneSiteMarginal N β := by
  let _ := coulombOneSiteMarginal_isProbability (N := N) hβ
  have hm := (coulombFrozenFirst_measurePreserving (N := N) hβ).symm
  have hi := hm.integrable_comp_of_integrable hF
  have h := Measure.integral_compProd hi
  have he := hm.integral_comp' F
  dsimp only [Function.comp_apply] at h
  rw [he] at h
  simpa only [coulombFrozenFirst_symm_apply] using h

end RepulsiveCoulomb
