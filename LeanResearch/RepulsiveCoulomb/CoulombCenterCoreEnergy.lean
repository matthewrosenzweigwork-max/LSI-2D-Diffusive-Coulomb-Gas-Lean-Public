import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeCore
import LeanResearch.RepulsiveCoulomb.CoulombCutoffEnergy

/-! Fubini and integrability for the actual two parts of a physical core
energy. Every signed integral used in tensorization is justified here. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

theorem coulombCenterChart_symm_function (e : CoulombCenterRotation n) :
    ((coulombCenterChart e).symm : ℂ × CoulombConfig n → CoulombConfig (n + 1)) =
      fun p => coulombCenterInsert e p.1 p.2 := by
  funext p
  exact coulombCenterChart_symm_apply e p.1 p.2

def coulombCenterCoreCenterEnergy (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (p : ℂ × CoulombConfig n) : ℝ :=
  ‖e (gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2)) 0‖ ^ 2

def coulombCenterCoreRelativeEnergy (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (p : ℂ × CoulombConfig n) : ℝ :=
  ‖coulombTail (e (gradient (φ : CoulombConfig (n + 1) → ℝ)
    (coulombCenterInsert e p.1 p.2)))‖ ^ 2

theorem coulombCenterCoreEnergy_sum (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (p : ℂ × CoulombConfig n) :
    coulombCenterCoreCenterEnergy e φ p + coulombCenterCoreRelativeEnergy e φ p =
      ‖gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2)‖ ^ 2 := by
  have h := coulombInsertZero_norm_sq
    (e (gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2)) 0)
    (coulombTail (e (gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2))))
  rw [coulombInsertZero_head_tail, e.norm_map] at h
  exact h.symm

theorem coulombCenterCoreCenterEnergy_integrable (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) :
    Integrable (coulombCenterCoreCenterEnergy e φ)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) := by
  letI := coulombMeasure_isProbability (N := n + 1) hβ
  have hg : MemLp (fun z => gradient (φ : CoulombConfig (n + 1) → ℝ) z) 2
      (coulombMeasure (n + 1) β) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  have heG := hg.continuousLinearMap_comp e.toContinuousLinearEquiv.toContinuousLinearMap
  have hp := (heG.continuousLinearMap_comp (coulombCoordinate 0)).norm.integrable_sq
  have h := (coulombCenter_gibbsMeasurePreserving e he hβ).symm.integrable_comp_of_integrable hp
  simp only [Function.comp_def, coulombCenterChart_symm_function, coulombCoordinate_apply] at h
  convert! h using 1

theorem coulombCenterCoreRelativeEnergy_integrable (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) :
    Integrable (coulombCenterCoreRelativeEnergy e φ)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) := by
  letI := coulombMeasure_isProbability (N := n + 1) hβ
  have hg : MemLp (fun z => gradient (φ : CoulombConfig (n + 1) → ℝ) z) 2
      (coulombMeasure (n + 1) β) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  have ht : Integrable (fun p : ℂ × CoulombConfig n =>
      ‖gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e p.1 p.2)‖ ^ 2)
      ((coulombCenterGaussian β).prod (coulombCenterRelativeMeasure e β)) := by
    have h := (coulombCenter_gibbsMeasurePreserving e he hβ).symm.integrable_comp_of_integrable
      hg.norm.integrable_sq
    simpa only [Function.comp_def, coulombCenterChart_symm_function] using h
  have hs := ht.sub (coulombCenterCoreCenterEnergy_integrable e he hβ φ)
  convert hs using 1
  funext p
  dsimp only [Pi.sub_apply]
  have h := coulombCenterCoreEnergy_sum e φ p
  linarith

theorem coulombCenterCoreEnergy_fubini (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) :
    (∫ r, ∫ c, coulombCenterCoreCenterEnergy e φ (c, r) ∂coulombCenterGaussian β
      ∂coulombCenterRelativeMeasure e β) +
    (∫ c, ∫ r, coulombCenterCoreRelativeEnergy e φ (c, r)
      ∂coulombCenterRelativeMeasure e β ∂coulombCenterGaussian β) =
      ∫ z, ‖gradient (φ : CoulombConfig (n + 1) → ℝ) z‖ ^ 2 ∂coulombMeasure (n + 1) β := by
  letI := coulombCenterGaussian_isProbability hβ
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  have hA := coulombCenterCoreCenterEnergy_integrable e he hβ φ
  have hB := coulombCenterCoreRelativeEnergy_integrable e he hβ φ
  rw [← integral_prod_symm _ hA, ← integral_prod _ hB, ← integral_add hA hB]
  simp_rw [coulombCenterCoreEnergy_sum]
  have h := (coulombCenter_gibbsMeasurePreserving e he hβ).symm.integral_comp'
    (fun z => ‖gradient (φ : CoulombConfig (n + 1) → ℝ) z‖ ^ 2)
  simpa only [Function.comp_def, coulombCenterChart_symm_function] using h

end RepulsiveCoulomb
