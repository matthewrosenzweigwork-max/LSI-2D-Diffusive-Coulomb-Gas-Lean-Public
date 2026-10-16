module

public import LeanResearch.RepulsiveCoulomb.DbarBranchBoundedFunctionalFactor
public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryClosedGraphSeparation
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

/-! Hahn-Banach and Riesz produce an actual graph solution from a bounded
adjoint pairing. The graph is tested in the genuine Hilbert product via the
previous separation theorem; no range-closedness assumption is introduced. -/
noncomputable section
open InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

theorem dbarClosedGraph_solution_of_pairing_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (G : ClosedSubmodule ℂ (E × F)) (d : F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v, (u, v) ∈ G.toSubmodule.adjoint → ‖inner ℂ d u‖ ≤ C * ‖v‖) :
    ∃ f : E, (f, d) ∈ G ∧ ‖f‖ ≤ C := by
  let D : Submodule ℂ (F × E) := G.toSubmodule.adjoint
  let Q : D →ₗ[ℂ] E := (LinearMap.snd ℂ F E).comp D.subtype
  let P : D →ₗ[ℂ] ℂ := (innerSL ℂ d).toLinearMap.comp ((LinearMap.fst ℂ F E).comp D.subtype)
  have hb (J : D) : ‖P J‖ ≤ C * ‖Q J‖ := hbound J.val.1 J.val.2 J.property
  obtain ⟨ℓ, hℓ, hnorm⟩ := dbarLinearMap_exists_bounded_factor Q P hC hb
  let f : E := (InnerProductSpace.toDual ℂ E).symm ℓ
  have hf : ‖f‖ ≤ C := ((InnerProductSpace.toDual ℂ E).symm.norm_map ℓ).trans_le hnorm
  refine ⟨f, ?_, hf⟩
  apply dbarClosedGraph_mem_of_adjoint_tests G f d
  intro u v huv
  have he := hℓ (⟨(u, v), huv⟩ : D)
  change ℓ v = inner ℂ d u at he
  have hinner : inner ℂ f v = inner ℂ d u := InnerProductSpace.toDual_symm_apply.trans he
  have hc := congrArg (starRingEnd ℂ) hinner
  simpa only [inner_conj_symm] using hc

end RepulsiveCoulomb
