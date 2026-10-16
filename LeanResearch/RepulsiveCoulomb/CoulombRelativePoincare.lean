import LeanResearch.RepulsiveCoulomb.CoulombRelativeCore
import LeanResearch.RepulsiveCoulomb.CoulombRelativeKernel

/-! Relative conditional PI with the exact unscaled full-gradient convention. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombRelativeCore_gradient_norm_sq {N : ℕ} (a : Fin (N + N + 1) → ℝ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) (c u : ℂ) (y : CoulombConfig N) :
    ‖gradient (coulombRelativeCore a φ c y : ℂ → ℝ) u‖ ^ 2 =
      (1 / 2 : ℝ) * ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2 := by
  rw [coulombRelativeCore_gradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)), mul_pow, inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

theorem coulomb_relative_core_uniform_poincare {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
    variance (fun u : ℂ => φ (coulombRelativeInsert c u y)) (coulombRelativeKernel N β hβ (c, y)) ≤
      (P / 2) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) := by
  obtain ⟨P, hP, hp⟩ := pointCore_uniform_poincare (Q := 2 * β) hβ
  refine ⟨P, hP, ?_⟩
  intro N c y φ
  let a := coulombRelativeExponents N β
  let ψ := coulombRelativeCore a φ c y
  have hQ : ∑ j, a j ≤ 2 * β := (coulombRelative_exponent_sum_lt N hβ).le
  have h := hp (N + N + 1) a (coulombRelativeExponents_nonneg N hβ.le)
    (coulombRelativeRoots c y) hQ ψ
  have he : (∫ u, ‖gradient (ψ : ℂ → ℝ) u‖ ^ 2 ∂pointMeasure β a (coulombRelativeRoots c y)) =
      (1 / 2 : ℝ) * (∫ u, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c u y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) := by
    rw [coulombRelativeKernel_apply, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => coulombRelativeCore_gradient_norm_sq a φ c u y)
  rw [he, coulombRelativeKernel_apply] at h
  rw [coulombRelativeKernel_apply]
  convert h using 1 <;> first | rfl | ring

end RepulsiveCoulomb

