import LeanResearch.RepulsiveCoulomb.EuclideanChartTransition
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Hausdorff

/-! SOURCE-ONLY, UNCOMPILED. Genuine local Euclidean-motion formulas on an
open connected region propagate to one full motion. Equality is tested as
an ambient open germ, never merely on a seam, so reflections cause no false
uniqueness claim. The resulting equality extends to boundary closures. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_euclideanMotion_eqOn_of_local_germs
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : ℂ → ℂ)
    (hlocal : ∀ x ∈ U, ∃ e : ℂ ≃ᵢ ℂ, f =ᶠ[𝓝 x] (e : ℂ → ℂ)) :
    ∃ e : ℂ ≃ᵢ ℂ, EqOn f e U := by
  classical
  let T : U → (ℂ ≃ᵢ ℂ) := fun x ↦ Classical.choose (hlocal x.1 x.2)
  have hT (x : U) : f =ᶠ[𝓝 x.1] (T x : ℂ → ℂ) := Classical.choose_spec (hlocal x.1 x.2)
  have hlc : IsLocallyConstant T := by
    apply (IsLocallyConstant.iff_eventually_eq T).mpr
    intro x
    have hnear : ∀ᶠ y in 𝓝 x.1, f =ᶠ[𝓝 y] (T x : ℂ → ℂ) :=
      eventually_eventuallyEq_nhds.mpr (hT x)
    filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually hnear] with y hy
    exact euclideanIsometryEquiv_eq_of_eventuallyEq ((hT y).symm.trans hy)
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨T ⟨x₀, hx₀⟩, fun x hx ↦ ?_⟩
  have heq := hlc.apply_eq_of_preconnectedSpace (⟨x, hx⟩ : U) ⟨x₀, hx₀⟩
  exact (hT ⟨x, hx⟩).self_of_nhds.trans (congrArg (fun e : ℂ ≃ᵢ ℂ ↦ e x) heq)

/-- Local continuity on the closed piece suffices for boundary extension;
there is no assertion about a function's arbitrary outside values. -/
theorem exists_euclideanMotion_eqOn_closure_of_local_germs
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : ℂ → ℂ) (hf : ContinuousOn f (closure U))
    (hlocal : ∀ x ∈ U, ∃ e : ℂ ≃ᵢ ℂ, f =ᶠ[𝓝 x] (e : ℂ → ℂ)) :
    ∃ e : ℂ ≃ᵢ ℂ, EqOn f e (closure U) := by
  obtain ⟨e, he⟩ := exists_euclideanMotion_eqOn_of_local_germs hU hconn hne f hlocal
  exact ⟨e, he.of_subset_closure hf e.continuous.continuousOn subset_closure subset_rfl⟩

end RepulsiveCoulomb
