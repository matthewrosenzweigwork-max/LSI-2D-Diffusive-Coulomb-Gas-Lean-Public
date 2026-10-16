import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCore
import LeanResearch.RepulsiveCoulomb.CoulombPotentialLaplacian
import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.WeakDeriv.Basic

/-! Actual directional Haar integration by parts for the full particle
potential. Every product is supported inside the collision-free open set. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombCoreSquare {N : ℕ} (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => φ z ^ 2, φ.contDiff.pow 2,
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp), by
      have h : tsupport (fun z : CoulombConfig N => φ z * φ z) ⊆ coulombDomain N :=
        tsupport_mul_subset_left.trans φ.tsupport_subset
      simpa only [pow_two] using h⟩

theorem coulombCoreSquare_apply {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    coulombCoreSquare φ z = φ z ^ 2 := rfl

theorem coulombCoreSquare_lineDeriv {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z v : CoulombConfig N) :
    lineDeriv ℝ (coulombCoreSquare φ : CoulombConfig N → ℝ) z v =
      2 * φ z * fderiv ℝ (φ : CoulombConfig N → ℝ) z v := by
  have h := (((φ.contDiff.differentiable (by simp) z).hasFDerivAt.pow 2).hasLineDerivAt v).lineDeriv
  change lineDeriv ℝ (fun x : CoulombConfig N => φ x ^ 2) z v = _
  simpa using h

theorem coulombPotential_component_contDiffAt_one {N : ℕ} (β : ℝ)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    ContDiffAt ℝ 1 (fun x => fderiv ℝ (coulombPotential β) x v) z := by
  have hU : ContDiffAt ℝ 2 (coulombPotential β) z :=
    (coulombPotential_contDiffAt β hz).of_le (by simp)
  exact (hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem coulombPotential_component_locallyIntegrable {N : ℕ} (β : ℝ)
    (v : CoulombConfig N) :
    LocallyIntegrableOn (fun x => fderiv ℝ (coulombPotential β) x v)
      (coulombDomain N) volume := by
  have hc : ContinuousOn (fun x => fderiv ℝ (coulombPotential β) x v) (coulombDomain N) :=
    fun x hx => (coulombPotential_component_contDiffAt_one β hx v).continuousAt.continuousWithinAt
  exact hc.locallyIntegrableOn (coulombDomain N).isOpen.measurableSet

theorem coulombPotential_component_derivative_locallyIntegrable {N : ℕ} (β : ℝ)
    (v w : CoulombConfig N) :
    LocallyIntegrableOn (fun x => fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y v) x w)
      (coulombDomain N) volume := by
  have hc : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y v) x w)
      (coulombDomain N) := by
    intro x hx
    exact (((coulombPotential_component_contDiffAt_one β hx v).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const).continuousWithinAt
  exact hc.locallyIntegrableOn (coulombDomain N).isOpen.measurableSet

theorem coulombPotential_component_weakLineDeriv {N : ℕ} (β : ℝ) (v : CoulombConfig N) :
    TauCeti.HasWeakLineDerivOn volume (coulombDomain N)
      (fun x => fderiv ℝ (coulombPotential β) x v)
      (fun x => fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y v) x v) v := by
  apply TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
    (coulombPotential_component_locallyIntegrable β v)
    (coulombPotential_component_derivative_locallyIntegrable β v v)
  intro x hx
  exact ((coulombPotential_component_contDiffAt_one β hx v).differentiableAt_one).hasFDerivAt.hasLineDerivAt v

theorem coulombCoreSquare_potential_integrationByParts {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (v : CoulombConfig N) :
    (∫ x : CoulombConfig N, (2 * φ x * fderiv ℝ (φ : CoulombConfig N → ℝ) x v) *
      fderiv ℝ (coulombPotential β) x v) =
      -(∫ x : CoulombConfig N, φ x ^ 2 *
        fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y v) x v) := by
  have h := (coulombPotential_component_weakLineDeriv β v).integral_lineDeriv_smul_eq_neg_integral_smul
    (coulombCoreSquare φ)
  simpa only [coulombCoreSquare_lineDeriv, coulombCoreSquare_apply, smul_eq_mul] using h

end RepulsiveCoulomb
