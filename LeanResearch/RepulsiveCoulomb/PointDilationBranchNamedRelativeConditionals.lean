import LeanResearch.RepulsiveCoulomb.PointDilationBranchNamedConstants
import LeanResearch.RepulsiveCoulomb.CoulombRelativePoincare

/-! RECORDS-ONLY UNCOMPILED. Literal named relative constants from the single
chosen unit pair. The fixed and compact-temperature conditional PI and core
relative-gradient bounds use exactly C_wt(beta,2 beta) and C_wt(1,2 b)/a. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def pointDilationBranchCrel (β : ℝ) : ℝ := pointDilationBranchCwt β (2 * β)

def pointDilationBranchCrelInterval (a b : ℝ) : ℝ := pointDilationBranchCwt 1 (2 * b) / a

theorem pointDilationBranchCrel_pos {β : ℝ} (hβ : 0 < β) : 0 < pointDilationBranchCrel β :=
  pointDilationBranchCwt_pos hβ (2 * β)

theorem pointDilationBranchCrelInterval_eq (a b : ℝ) :
    pointDilationBranchCrelInterval a b = pointDilationBranchCwt a (2 * b) := by
  simp only [pointDilationBranchCrelInterval, pointDilationBranchCwt, div_one]

theorem pointDilationBranchCrelInterval_pos {a b : ℝ} (ha : 0 < a) :
    0 < pointDilationBranchCrelInterval a b := by
  rw [pointDilationBranchCrelInterval_eq]
  exact pointDilationBranchCwt_pos ha (2 * b)

theorem pointDilationBranch_named_relative_full {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (p : ℂ × CoulombConfig N)
    (u : PointFormDomain hβ (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2)) :
    variance (pointFormValueL hβ (coulombRelativeExponents_nonneg N hβ.le)
      (coulombRelativeRoots p.1 p.2) u : ℂ → ℝ) (coulombRelativeKernel N β hβ p) ≤
      pointDilationBranchCrel β * pointFormEnergy hβ (coulombRelativeExponents_nonneg N hβ.le)
        (coulombRelativeRoots p.1 p.2) u := by
  have h := (pointDilationBranch_named_weighted_inequalities (2 * β) hβ (N + N + 1)
    (coulombRelativeExponents N β) (coulombRelativeExponents_nonneg N hβ.le)
    (coulombRelativeRoots p.1 p.2) (coulombRelative_exponent_sum_lt N hβ).le u).1
  simpa only [coulombRelativeKernel_apply, pointDilationBranchCrel] using h

theorem pointDilationBranch_named_relative_full_interval {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b)
    (N : ℕ) (p : ℂ × CoulombConfig N)
    (u : PointFormDomain hβ (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2)) :
    variance (pointFormValueL hβ (coulombRelativeExponents_nonneg N hβ.le)
      (coulombRelativeRoots p.1 p.2) u : ℂ → ℝ) (coulombRelativeKernel N β hβ p) ≤
      pointDilationBranchCrelInterval a b * pointFormEnergy hβ (coulombRelativeExponents_nonneg N hβ.le)
        (coulombRelativeRoots p.1 p.2) u := by
  have hQ : ∑ j, coulombRelativeExponents N β j ≤ 2 * b :=
    (coulombRelative_exponent_sum_lt N hβ).le.trans (mul_le_mul_of_nonneg_left hhi (by norm_num))
  have h := (pointDilationBranch_named_full_above (2 * b) ha hβ hlo (N + N + 1)
    (coulombRelativeExponents N β) (coulombRelativeExponents_nonneg N hβ.le)
    (coulombRelativeRoots p.1 p.2) hQ u).1
  simpa only [coulombRelativeKernel_apply, pointDilationBranchCrelInterval_eq] using h

theorem pointDilationBranch_relative_core_of_full {β P : ℝ} (hβ : 0 < β)
    (hfull : ∀ (N : ℕ) (p : ℂ × CoulombConfig N)
      (u : PointFormDomain hβ (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2)),
      variance (pointFormValueL hβ (coulombRelativeExponents_nonneg N hβ.le)
        (coulombRelativeRoots p.1 p.2) u : ℂ → ℝ) (coulombRelativeKernel N β hβ p) ≤
        P * pointFormEnergy hβ (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2) u) :
    ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      variance (fun w : ℂ => φ (coulombRelativeInsert c w y)) (coulombRelativeKernel N β hβ (c, y)) ≤
        (P / 2) * (∫ w, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) 0 -
          gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) := by
  intro N c y φ
  let a := coulombRelativeExponents N β
  let ψ := coulombRelativeCore a φ c y
  have ha := coulombRelativeExponents_nonneg N hβ.le
  have h := hfull N (c, y) (pointFormCore hβ ha (coulombRelativeRoots c y) ψ)
  simp only [coulombRelativeKernel_apply] at h
  rw [pointFormCore_variance, pointFormCore_energy_eq_integral] at h
  have he : (∫ w, ‖gradient (ψ : ℂ → ℝ) w‖ ^ 2 ∂pointMeasure β a (coulombRelativeRoots c y)) =
      (1 / 2 : ℝ) * (∫ w, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) 0 -
        gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) := by
    rw [coulombRelativeKernel_apply, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => coulombRelativeCore_gradient_norm_sq a φ c w y)
  rw [he, coulombRelativeKernel_apply] at h
  rw [coulombRelativeKernel_apply]
  convert h using 1 <;> first | rfl | ring

theorem pointDilationBranch_named_relative_core {β : ℝ} (hβ : 0 < β) :
    ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      variance (fun w : ℂ => φ (coulombRelativeInsert c w y)) (coulombRelativeKernel N β hβ (c, y)) ≤
        (pointDilationBranchCrel β / 2) * (∫ w, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) 0 -
          gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) :=
  pointDilationBranch_relative_core_of_full hβ (pointDilationBranch_named_relative_full hβ)

theorem pointDilationBranch_named_relative_core_interval {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b) :
    ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      variance (fun w : ℂ => φ (coulombRelativeInsert c w y)) (coulombRelativeKernel N β hβ (c, y)) ≤
        (pointDilationBranchCrelInterval a b / 2) *
          (∫ w, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) 0 -
            gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) (Fin.succ 0)‖ ^ 2
            ∂coulombRelativeKernel N β hβ (c, y)) :=
  pointDilationBranch_relative_core_of_full hβ
    (pointDilationBranch_named_relative_full_interval ha hβ hlo hhi)

end RepulsiveCoulomb
