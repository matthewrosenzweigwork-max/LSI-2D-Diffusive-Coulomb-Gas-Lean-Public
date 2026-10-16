import LeanResearch.RepulsiveCoulomb.CoulombRelativeDisintegration
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual relative joint law and signed tower with genuine integrability. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal ProbabilityTheory
namespace RepulsiveCoulomb

theorem coulomb_relative_joint_law {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Measure.map (coulombRelativeFrozenFirst N) (coulombMeasure (N + 2) β) =
      coulombRelativeMarginal N β ⊗ₘ coulombRelativeKernel N β hβ := by
  let _ := coulombRelativeMarginal_isProbability (N := N) hβ
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (coulombRelativeFrozenFirst N).measurable, Measure.lintegral_compProd hF]
  have h := coulomb_relative_tower hβ (hF.comp (coulombRelativeFrozenFirst N).measurable)
  simpa only [Function.comp_apply, coulombRelativeFrozenFirst_insert] using h

theorem coulombRelativeFrozenFirst_gibbsMeasurePreserving {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    MeasurePreserving (coulombRelativeFrozenFirst N) (coulombMeasure (N + 2) β)
      (coulombRelativeMarginal N β ⊗ₘ coulombRelativeKernel N β hβ) :=
  ⟨(coulombRelativeFrozenFirst N).measurable, coulomb_relative_joint_law hβ⟩

theorem coulomb_relative_slice_integrability {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 2) → ℝ} (hF : Integrable F (coulombMeasure (N + 2) β)) :
    (∀ᵐ y ∂coulombRelativeMarginal N β,
      Integrable (fun w => F (coulombRelativeInsert y.1 w y.2)) (coulombRelativeKernel N β hβ y)) ∧
      Integrable (fun y => ∫ w, |F (coulombRelativeInsert y.1 w y.2)| ∂coulombRelativeKernel N β hβ y)
        (coulombRelativeMarginal N β) := by
  let _ := coulombRelativeMarginal_isProbability (N := N) hβ
  have hi := (coulombRelativeFrozenFirst_gibbsMeasurePreserving (N := N) hβ).symm.integrable_comp_of_integrable hF
  have h := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  simpa only [Function.comp_apply, Function.uncurry_apply_pair, coulombRelativeFrozenFirst_symm_apply, Real.norm_eq_abs] using h

theorem coulomb_relative_integral_tower {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 2) → ℝ} (hF : Integrable F (coulombMeasure (N + 2) β)) :
    (∫ z, F z ∂coulombMeasure (N + 2) β) =
      ∫ y : ℂ × CoulombConfig N, (∫ w : ℂ, F (coulombRelativeInsert y.1 w y.2) ∂coulombRelativeKernel N β hβ y)
        ∂coulombRelativeMarginal N β := by
  let _ := coulombRelativeMarginal_isProbability (N := N) hβ
  have hm := (coulombRelativeFrozenFirst_gibbsMeasurePreserving (N := N) hβ).symm
  have hi := hm.integrable_comp_of_integrable hF
  have h := Measure.integral_compProd hi
  have he := hm.integral_comp' F
  dsimp only [Function.comp_apply] at h
  rw [he] at h
  simpa only [coulombRelativeFrozenFirst_symm_apply] using h

end RepulsiveCoulomb
