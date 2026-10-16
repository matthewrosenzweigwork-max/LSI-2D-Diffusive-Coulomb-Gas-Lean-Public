module

public import LeanResearch.RepulsiveCoulomb.CoulombAssociatedVariational
public import LeanResearch.RepulsiveCoulomb.CoulombFormCenter
public import LeanResearch.RepulsiveCoulomb.DbarBranchFormKernelConstants

@[expose] public section

/-! The actual associated operator has precisely constant zero modes.
No Poincare gap is used to prove the kernel assertion. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombAssociatedOperator_zero_constant (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : (coulombAssociatedOperator N hβ).domain)
    (hu : coulombAssociatedOperator N hβ u = 0) :
    ∃ a : ℝ, (u : Lp ℝ 2 (coulombMeasure N β)) =ᵐ[coulombMeasure N β] fun _ => a := by
  have hp := (coulombAssociatedOperator N hβ).mem_graph u
  rw [coulombAssociatedOperator_graph] at hp
  obtain ⟨v, hv, he⟩ := (coulombAssociatedGraph_variational hβ _ _).mp hp
  have hz : coulombFormGradientL N hβ v = 0 := by
    have h := he v
    rw [hu, inner_zero_left] at h
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp h
  obtain ⟨a, ha⟩ := coulombForm_zero_gradient_constant hβ v hz
  exact ⟨a, by simpa only [hv] using ha⟩

theorem coulombAssociatedOperator_constant_zero (N : ℕ) {β : ℝ} (hβ : 0 < β) (a : ℝ) :
    ∃ u : (coulombAssociatedOperator (N + 2) hβ).domain,
      (u : Lp ℝ 2 (coulombMeasure (N + 2) β)) = a • poleBranchRealOne (N + 2) hβ ∧
      coulombAssociatedOperator (N + 2) hβ u = 0 := by
  have hp : (a • poleBranchRealOne (N + 2) hβ, (0 : Lp ℝ 2 (coulombMeasure (N + 2) β))) ∈
      coulombAssociatedGraph (N + 2) hβ := by
    apply (coulombAssociatedGraph_variational hβ _ _).mpr
    refine ⟨a • coulombConstantForm N hβ, ?_, ?_⟩
    · rw [map_smul, coulombConstantForm_value_eq_realOne]
    · intro v
      simp only [coulombFormEnergyPair, map_smul, coulombConstantForm_gradient,
        smul_zero, inner_zero_left]
  rw [← coulombAssociatedOperator_graph] at hp
  exact (LinearPMap.mem_graph_iff _).mp hp

end RepulsiveCoulomb
