import LeanResearch.RepulsiveCoulomb.CoulombAssociatedSelfAdjoint

/-! Exact variational association and both inverse identities for I+A.
Together with compactness of R, these express the literal compact resolvent
at spectral parameter -1 (whose conventional signed resolvent is -R). -/
noncomputable section
open Set MeasureTheory InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombAssociatedGraph_variational {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (x g : Lp ℝ 2 (coulombMeasure N β)) :
    (x, g) ∈ coulombAssociatedGraph N hβ ↔
      ∃ u : CoulombFormDomain N hβ, coulombFormValueL N hβ u = x ∧
        ∀ v : CoulombFormDomain N hβ,
          coulombFormEnergyPair N hβ u v = inner ℝ g (coulombFormValueL N hβ v) := by
  constructor
  · intro hp
    obtain ⟨h, hx, hg⟩ := (coulombAssociatedGraph_mem hβ x g).mp hp
    refine ⟨(coulombFormValueL N hβ).adjoint h, hx, ?_⟩
    intro v
    have hv := coulombFormResolvent_variational N hβ h v
    rw [← hg, inner_sub_left]
    linarith only [hv]
  · rintro ⟨u, hx, hu⟩
    have hi (v : CoulombFormDomain N hβ) :
        inner ℝ u v = inner ℝ ((coulombFormValueL N hβ).adjoint (x + g)) v := by
      calc
        _ = inner ℝ (coulombFormValueL N hβ u) (coulombFormValueL N hβ v) +
            coulombFormEnergyPair N hβ u v := coulombForm_inner_eq N hβ u v
        _ = inner ℝ x (coulombFormValueL N hβ v) + inner ℝ g (coulombFormValueL N hβ v) :=
          congrArg₂ (fun a b : ℝ => a + b)
            (congrArg (fun w : Lp ℝ 2 (coulombMeasure N β) => inner ℝ w (coulombFormValueL N hβ v)) hx)
            (hu v)
        _ = inner ℝ (x + g) (coulombFormValueL N hβ v) :=
          (inner_add_left x g (coulombFormValueL N hβ v)).symm
        _ = _ := (ContinuousLinearMap.adjoint_inner_left (coulombFormValueL N hβ) v (x + g)).symm
    have he : u = (coulombFormValueL N hβ).adjoint (x + g) := ext_inner_right ℝ hi
    have hR : coulombFormResolvent N hβ (x + g) = x :=
      (congrArg (coulombFormValueL N hβ) he.symm).trans hx
    exact (coulombAssociatedGraph_mem hβ x g).mpr ⟨x + g, hR, by rw [hR]; abel⟩

theorem coulombAssociatedOperator_nonneg (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : (coulombAssociatedOperator N hβ).domain) :
    0 ≤ inner ℝ (coulombAssociatedOperator N hβ u) (u : Lp ℝ 2 (coulombMeasure N β)) := by
  have hp := (coulombAssociatedOperator N hβ).mem_graph u
  rw [coulombAssociatedOperator_graph] at hp
  obtain ⟨v, hv, he⟩ := (coulombAssociatedGraph_variational hβ _ _).mp hp
  rw [← hv, ← he v, coulombFormEnergyPair, real_inner_self_eq_norm_sq]
  positivity

theorem coulombAssociatedGraph_inverse {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (x g : Lp ℝ 2 (coulombMeasure N β)) :
    (x, g) ∈ coulombAssociatedGraph N hβ ↔ coulombFormResolvent N hβ (x + g) = x := by
  rw [coulombAssociatedGraph_mem]
  constructor
  · rintro ⟨h, hx, hg⟩
    have he : x + g = h := by rw [← hx, ← hg]; abel
    rw [he, hx]
  · intro hx
    exact ⟨x + g, hx, by rw [hx]; abel⟩

theorem coulombFormResolvent_left_inverse (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : (coulombAssociatedOperator N hβ).domain) :
    coulombFormResolvent N hβ ((u : Lp ℝ 2 (coulombMeasure N β)) +
      coulombAssociatedOperator N hβ u) = u := by
  apply (coulombAssociatedGraph_inverse hβ _ _).mp
  rw [← coulombAssociatedOperator_graph]
  exact (coulombAssociatedOperator N hβ).mem_graph u

theorem coulombFormResolvent_right_inverse (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β)) :
    ∃ u : (coulombAssociatedOperator N hβ).domain,
      (u : Lp ℝ 2 (coulombMeasure N β)) = coulombFormResolvent N hβ f ∧
      (u : Lp ℝ 2 (coulombMeasure N β)) + coulombAssociatedOperator N hβ u = f := by
  have hp : (coulombFormResolvent N hβ f, f - coulombFormResolvent N hβ f) ∈
      (coulombAssociatedOperator N hβ).graph := by
    rw [coulombAssociatedOperator_graph]
    exact (coulombAssociatedGraph_mem hβ _ _).mpr ⟨f, rfl, rfl⟩
  obtain ⟨u, hu, hA⟩ := (LinearPMap.mem_graph_iff _).mp hp
  refine ⟨u, hu, ?_⟩
  change (u : Lp ℝ 2 (coulombMeasure N β)) = coulombFormResolvent N hβ f at hu
  change coulombAssociatedOperator N hβ u = f - coulombFormResolvent N hβ f at hA
  calc
    _ = coulombFormResolvent N hβ f + (f - coulombFormResolvent N hβ f) :=
      congrArg₂ (fun a b : Lp ℝ 2 (coulombMeasure N β) => a + b) hu hA
    _ = (f - coulombFormResolvent N hβ f) + coulombFormResolvent N hβ f := add_comm _ _
    _ = f := sub_add_cancel _ _

end RepulsiveCoulomb
