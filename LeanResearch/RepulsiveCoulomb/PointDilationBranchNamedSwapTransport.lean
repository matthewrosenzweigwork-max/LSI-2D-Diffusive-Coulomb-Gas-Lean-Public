module

public import LeanResearch.RepulsiveCoulomb.PointDilationBranchNamedRelativeConditionals
public import LeanResearch.RepulsiveCoulomb.CoulombFirstSwapBound

@[expose] public section

/-! RECORDS-ONLY UNCOMPILED. Constant-preserving conditional and first-pair
swap transport. P is supplied, never reselected. The factors are exactly 4 and 1/2. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointDilationBranch_relative_swap_of_core {β P : ℝ} (hβ : 0 < β)
    (hp : ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
    variance (fun u : ℂ => φ (coulombRelativeInsert c u y)) (coulombRelativeKernel N β hβ (c, y)) ≤
      (P / 2) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y))) :
    ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
    (∫ u, (φ (coulombRelativeInsert c u y) - φ (coulombRelativeInsert c (-u) y)) ^ 2
      ∂coulombRelativeKernel N β hβ (c, y)) ≤
      (2 * P) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) := by
  intro N c y φ
  let ψ := coulombRelativeCore (coulombRelativeExponents N β) φ c y
  have hm : MemLp (ψ : ℂ → ℝ) 2 (coulombRelativeKernel N β hβ (c, y)) :=
    ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  let e : ℂ ≃ᵐ ℂ := (LinearIsometryEquiv.neg ℝ : ℂ ≃ₗᵢ[ℝ] ℂ).toMeasurableEquiv
  have he : MeasurePreserving e (coulombRelativeKernel N β hβ (c, y))
      (coulombRelativeKernel N β hβ (c, y)) := coulombRelativeKernel_neg_measurePreserving hβ (c, y)
  have hs := measurePreserving_difference_le_variance (coulombRelativeKernel N β hβ (c, y)) e he hm
  have hpi := hp N c y φ
  change (∫ u, (φ (coulombRelativeInsert c u y) - φ (coulombRelativeInsert c (-u) y)) ^ 2
    ∂coulombRelativeKernel N β hβ (c, y)) ≤
    4 * variance (fun u => φ (coulombRelativeInsert c u y)) (coulombRelativeKernel N β hβ (c, y)) at hs
  calc
    _ ≤ _ := hs
    _ ≤ 4 * ((P / 2) * _) := mul_le_mul_of_nonneg_left hpi (by norm_num)
    _ = _ := by ring

theorem pointDilationBranch_first_swap_of_relative {β P : ℝ} (hβ : 0 < β)
    (hp : ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
    (∫ u, (φ (coulombRelativeInsert c u y) - φ (coulombRelativeInsert c (-u) y)) ^ 2
      ∂coulombRelativeKernel N β hβ (c, y)) ≤
      (2 * P) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y))) :
    ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      (∫ z, (φ z - φ (coulombSwapFirst N z)) ^ 2 ∂coulombMeasure (N + 2) β) ≤
        (2 * P) * (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z 0 -
          gradient (φ : CoulombConfig (N + 2) → ℝ) z (Fin.succ 0)‖ ^ 2
            ∂coulombMeasure (N + 2) β) := by
  intro N φ
  have hF := coulomb_core_first_swap_integrable hβ φ
  have hG := coulomb_core_pair_gradient_integrable hβ φ 0 (Fin.succ 0)
  have hFo := (coulomb_relative_slice_integrability hβ hF).2
  have hGo := (coulomb_relative_slice_integrability hβ hG).2
  simp only [abs_sq] at hFo hGo
  rw [coulomb_relative_integral_tower hβ hF, coulomb_relative_integral_tower hβ hG,
    ← integral_const_mul]
  apply integral_mono hFo (hGo.const_mul (2 * P))
  intro p
  simpa only [coulombSwapFirst_relative] using hp N p.1 p.2 φ

end RepulsiveCoulomb
