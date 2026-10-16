module

public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-! Compatible local holomorphic extensions across a dense domain glue without
any prior global-extension hypothesis. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem poleBranch_glue_local_extensions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {V : Set E} (hV : Dense V)
    (hlocal : ∀ x : E, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → ℂ, DifferentiableOn ℂ g U ∧ EqOn g f (U ∩ V)) :
    ∃ F : E → ℂ, Differentiable ℂ F ∧ EqOn F f V := by
  classical
  choose U hU hxU g hg heq using hlocal
  let F : E → ℂ := fun x => g x x
  have hcompat (x y : E) : EqOn (g x) (g y) (U x ∩ U y) := by
    have h : EqOn (g x) (g y) ((U x ∩ U y) ∩ V) := by
      intro z hz
      exact (heq x ⟨hz.1.1, hz.2⟩).trans (heq y ⟨hz.1.2, hz.2⟩).symm
    exact h.of_subset_closure ((hg x).continuousOn.mono inter_subset_left)
      ((hg y).continuousOn.mono inter_subset_right) inter_subset_left
      (hV.open_subset_closure_inter ((hU x).inter (hU y)))
  have hFx (x : E) : EqOn F (g x) (U x) := by
    intro y hy
    exact (hcompat y x) ⟨hxU y, hy⟩
  refine ⟨F, ?_, ?_⟩
  · intro x
    exact ((hg x).differentiableAt ((hU x).mem_nhds (hxU x))).congr_of_eventuallyEq
      ((hFx x).eventuallyEq_of_mem ((hU x).mem_nhds (hxU x)))
  · intro x hx
    exact heq x ⟨hxU x, hx⟩

end RepulsiveCoulomb
