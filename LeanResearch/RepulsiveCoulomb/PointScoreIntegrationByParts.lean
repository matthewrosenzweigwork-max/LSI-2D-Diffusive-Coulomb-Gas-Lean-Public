module

public import LeanResearch.RepulsiveCoulomb.PointScoreDivergence
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.WeakDeriv.Basic

@[expose] public section

/-! Actual Haar integration by parts against the original smooth core, with
local score regularity and integrability proved on exactly its open domain. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def pointCoreSquare {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) : TestFunction (pointDomain a y) ℝ ⊤ :=
  ⟨fun z => φ z ^ 2, φ.contDiff.pow 2,
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp), by
      have h : tsupport (fun z : ℂ => φ z * φ z) ⊆ pointDomain a y :=
        tsupport_mul_subset_left.trans φ.tsupport_subset
      simpa only [pow_two] using h⟩

theorem pointCoreSquare_apply {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) : pointCoreSquare a y φ z = φ z ^ 2 := rfl

theorem pointCoreSquare_lineDeriv {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (z v : ℂ) :
    lineDeriv ℝ (pointCoreSquare a y φ : ℂ → ℝ) z v = 2 * φ z * fderiv ℝ (φ : ℂ → ℝ) z v := by
  have h := (((φ.contDiff.differentiable (by simp) z).hasFDerivAt.pow 2).hasLineDerivAt v).lineDeriv
  change lineDeriv ℝ (fun x : ℂ => φ x ^ 2) z v = _
  simpa using h

theorem pointScore_component_locallyIntegrable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : ℂ) :
    LocallyIntegrableOn (fun x => inner ℝ (pointScore γ a y x) v) (pointDomain a y) volume := by
  have hc : ContinuousOn (fun x => inner ℝ (pointScore γ a y x) v) (pointDomain a y) :=
    fun x hx => (pointScore_component_contDiffAt_one γ ha y hx v).continuousAt.continuousWithinAt
  exact hc.locallyIntegrableOn (pointDomain a y).isOpen.measurableSet

theorem pointScore_component_derivative_locallyIntegrable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v w : ℂ) :
    LocallyIntegrableOn (fun x => fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) v) x w)
      (pointDomain a y) volume := by
  have hc : ContinuousOn (fun x => fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) v) x w)
      (pointDomain a y) := by
    intro x hx
    exact (((pointScore_component_contDiffAt_one γ ha y hx v).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const).continuousWithinAt
  exact hc.locallyIntegrableOn (pointDomain a y).isOpen.measurableSet

theorem pointScore_component_weakLineDeriv {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (v : ℂ) :
    TauCeti.HasWeakLineDerivOn volume (pointDomain a y)
      (fun x => inner ℝ (pointScore γ a y x) v)
      (fun x => fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) v) x v) v := by
  apply TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
    (pointScore_component_locallyIntegrable γ ha y v)
    (pointScore_component_derivative_locallyIntegrable γ ha y v v)
  intro x hx
  exact ((pointScore_component_contDiffAt_one γ ha y hx v).differentiableAt_one).hasFDerivAt.hasLineDerivAt v

theorem pointCoreSquare_score_integrationByParts {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (v : ℂ) :
    (∫ x : ℂ, (2 * φ x * fderiv ℝ (φ : ℂ → ℝ) x v) * inner ℝ (pointScore γ a y x) v) =
      -(∫ x : ℂ, φ x ^ 2 * fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) v) x v) := by
  have h := (pointScore_component_weakLineDeriv γ ha y v).integral_lineDeriv_smul_eq_neg_integral_smul
    (pointCoreSquare a y φ)
  simpa only [pointCoreSquare_lineDeriv, pointCoreSquare_apply, smul_eq_mul] using h

theorem pointCore_score_directional_cross_integrable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (v : ℂ) :
    Integrable (fun x : ℂ => φ x * fderiv ℝ (φ : ℂ → ℝ) x v * inner ℝ (pointScore γ a y x) v) := by
  have h := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    (pointScore_component_locallyIntegrable γ ha y v) (pointCoreSquare a y φ) v
  have hi : Integrable (fun x : ℂ =>
      (2 * φ x * fderiv ℝ (φ : ℂ → ℝ) x v) * inner ℝ (pointScore γ a y x) v) := by
    simpa only [pointCoreSquare_lineDeriv, smul_eq_mul] using h
  convert! hi.const_mul (1 / 2 : ℝ) using 1
  funext x
  ring

theorem pointCore_score_divergence_integrable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (v : ℂ) :
    Integrable (fun x : ℂ => φ x ^ 2 *
      fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) v) x v) := by
  have h := TauCeti.integrable_smul_of_locallyIntegrableOn
    (pointScore_component_derivative_locallyIntegrable γ ha y v v) (pointCoreSquare a y φ)
  simpa only [pointCoreSquare_apply, smul_eq_mul] using h

end RepulsiveCoulomb
