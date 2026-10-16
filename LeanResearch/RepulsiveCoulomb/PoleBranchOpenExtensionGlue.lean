module

public import LeanResearch.RepulsiveCoulomb.PoleBranchExtensionGlue

@[expose] public section

/-! Local extensions on an open intermediate domain glue before the final
Hartogs step. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem poleBranch_glue_local_extensions_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {V W : Set E} (hV : Dense V) (hW : IsOpen W)
    (hlocal : ∀ x ∈ W, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ g : E → ℂ, DifferentiableOn ℂ g U ∧ EqOn g f (U ∩ V)) :
    ∃ F : E → ℂ, DifferentiableOn ℂ F W ∧ EqOn F f (W ∩ V) := by
  classical
  choose U hU hxU g hg heq using (fun x : W => hlocal x x.property)
  let F : E → ℂ := fun x => if hx : x ∈ W then g ⟨x, hx⟩ x else f x
  have hcompat (x y : W) : EqOn (g x) (g y) (U x ∩ U y) := by
    have h : EqOn (g x) (g y) ((U x ∩ U y) ∩ V) := by
      intro z hz
      exact (heq x ⟨hz.1.1, hz.2⟩).trans (heq y ⟨hz.1.2, hz.2⟩).symm
    exact h.of_subset_closure ((hg x).continuousOn.mono inter_subset_left)
      ((hg y).continuousOn.mono inter_subset_right) inter_subset_left
      (hV.open_subset_closure_inter ((hU x).inter (hU y)))
  have hFx (x : W) : EqOn F (g x) (U x ∩ W) := by
    intro y hy
    dsimp only [F]
    rw [dif_pos hy.2]
    exact (hcompat ⟨y, hy.2⟩ x) ⟨hxU ⟨y, hy.2⟩, hy.1⟩
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    let a : W := ⟨x, hx⟩
    have hn : U a ∩ W ∈ 𝓝 x := inter_mem ((hU a).mem_nhds (hxU a)) (hW.mem_nhds hx)
    exact (((hg a).differentiableAt ((hU a).mem_nhds (hxU a))).congr_of_eventuallyEq
      ((hFx a).eventuallyEq_of_mem hn)).differentiableWithinAt
  · intro x hx
    dsimp only [F]
    rw [dif_pos hx.1]
    exact heq ⟨x, hx.1⟩ ⟨hxU ⟨x, hx.1⟩, hx.2⟩

end RepulsiveCoulomb
