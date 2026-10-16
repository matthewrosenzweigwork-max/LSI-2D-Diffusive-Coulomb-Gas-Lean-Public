import LeanResearch.RepulsiveCoulomb.CoulombAssociatedGraph

/-! Self-adjointness of the literal unbounded graph built from the actual
variational resolvent. Dense domain is proved, never assumed. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombFormResolvent_inner_swap (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f g : Lp ℝ 2 (coulombMeasure N β)) :
    inner ℝ (coulombFormResolvent N hβ f) g = inner ℝ f (coulombFormResolvent N hβ g) := by
  rw [← ContinuousLinearMap.adjoint_inner_right (coulombFormResolvent N hβ),
    coulombFormResolvent_adjoint]

theorem coulombAssociatedGraph_adjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (coulombAssociatedGraph N hβ).adjoint = coulombAssociatedGraph N hβ := by
  ext p
  obtain ⟨y, z⟩ := p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro h
    have ho (k : Lp ℝ 2 (coulombMeasure N β)) :
        inner ℝ k (coulombFormResolvent N hβ (y + z) - y) = 0 := by
      have hh := h (coulombFormResolvent N hβ k) (k - coulombFormResolvent N hβ k)
        ((coulombAssociatedGraph_mem hβ _ _).mpr ⟨k, rfl, rfl⟩)
      change inner ℝ (k - coulombFormResolvent N hβ k) y -
        inner ℝ (coulombFormResolvent N hβ k) z = 0 at hh
      rw [inner_sub_left, coulombFormResolvent_inner_swap N hβ k y,
        coulombFormResolvent_inner_swap N hβ k z] at hh
      rw [map_add, inner_sub_right, inner_add_right]
      linarith only [hh]
    have he : coulombFormResolvent N hβ (y + z) = y :=
      sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp (ho _))
    apply (coulombAssociatedGraph_mem hβ y z).mpr
    refine ⟨y + z, he, ?_⟩
    rw [he]
    abel
  · intro hp a b hab
    obtain ⟨h, hy, hz⟩ := (coulombAssociatedGraph_mem hβ y z).mp hp
    obtain ⟨k, ha, hb⟩ := (coulombAssociatedGraph_mem hβ a b).mp hab
    change inner ℝ b y - inner ℝ a z = 0
    rw [← hy, ← hz, ← ha, ← hb, inner_sub_left, inner_sub_right,
      coulombFormResolvent_inner_swap N hβ k h]
    ring

theorem coulombAssociatedOperator_selfAdjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsSelfAdjoint (coulombAssociatedOperator N hβ) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (coulombAssociatedOperator_denseDomain N hβ),
    coulombAssociatedOperator_graph, coulombAssociatedGraph_adjoint]

end RepulsiveCoulomb
