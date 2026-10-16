module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelRepresentative
public import LeanResearch.RepulsiveCoulomb.DbarBranchHolomorphicWeakKernel

@[expose] public section

/-! Exact identification of the actual weak kernel with genuine holomorphic
weighted-L2 representatives, combining the independently proved directions. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombDbarWeakKernel_mem_iff_holomorphic {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    f ∈ coulombDbarWeakKernel N hβ ↔
      ∃ h : CoulombConfig N → ℂ, DifferentiableOn ℂ h (coulombDomain N) ∧
        f =ᵐ[coulombMeasure N β] h := by
  rw [coulombDbarWeakKernel_mem_iff]
  exact ⟨coulombWeakKernel_holomorphic_representative hβ f,
    fun ⟨h, hh, hrep⟩ => coulombHolomorphic_representative_mem_weakKernel hβ f hh hrep⟩

end RepulsiveCoulomb
