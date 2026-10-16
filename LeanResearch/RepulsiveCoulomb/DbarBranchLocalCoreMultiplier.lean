module

public import LeanResearch.RepulsiveCoulomb.CoulombDbarCore
public import LeanResearch.RepulsiveCoulomb.CoulombDensitySmooth

@[expose] public section

/-! Honest smooth core multipliers from functions smooth only on the collision
complement. Vanishing near the complement supplies global smoothness. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

def coulombComplexCoreMulLocal {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ where
  toFun z := a z * ψ z
  contDiff' := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport (ψ : CoulombConfig N → ℂ)
    · exact (ha z (ψ.tsupport_subset hz)).mul ψ.contDiff.contDiffAt
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      change a y * ψ y = 0
      rw [hy, Pi.zero_apply, mul_zero]
  hasCompactSupport' := ψ.hasCompactSupport.mul_left
  tsupport_subset' := tsupport_mul_subset_right.trans ψ.tsupport_subset

theorem coulombComplexCoreMulLocal_apply {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombComplexCoreMulLocal a ha ψ z = a z * ψ z := rfl

def coulombComplexCoreDensityMul {N : ℕ} (β : ℝ)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombComplexCoreMulLocal (fun z => (coulombDensity N β z : ℂ))
    (fun z hz => Complex.ofRealCLM.contDiff.contDiffAt.comp z ((coulombDensity_contDiffAt β hz).of_le le_top)) ψ

def coulombComplexCoreDensityDiv {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombComplexCoreMulLocal (fun z => (coulombDensity N β z : ℂ)⁻¹)
    (fun z hz => (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((coulombDensity_contDiffAt β hz).of_le le_top)).inv (by
        change (coulombDensity N β z : ℂ) ≠ 0
        exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz)))) ψ

theorem coulombComplexCoreDensityDiv_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombComplexCoreDensityDiv hβ ψ z = ψ z / (coulombDensity N β z : ℂ) := by
  change (coulombDensity N β z : ℂ)⁻¹ * ψ z = _
  rw [div_eq_mul_inv, mul_comm]

end RepulsiveCoulomb
