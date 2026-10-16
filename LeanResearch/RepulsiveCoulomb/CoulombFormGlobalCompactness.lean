module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoreCompactness

@[expose] public section

/-! Actual compactness of the full original closed form domain in Gibbs L2,
for each fixed particle number and positive temperature. Core approximation
and the genuine ground-state isometry preserve the original observable domain. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombFormValue_global_compact {N : ℕ} {β : ℝ} (hβ : 0 < β) (R : ℝ) :
    IsCompact (closure ((coulombFormValueL N hβ) ''
      {u : CoulombFormDomain N hβ | ‖u‖ ≤ R})) := by
  let K := closure ((coulombGroundStateCoreLp hβ) ''
    {φ : TestFunction (coulombDomain N) ℝ ⊤ | ‖coulombFormCore hβ φ‖ ≤ R + 1})
  have hK : IsCompact K := coulombGroundStateCore_compact hβ (R + 1)
  have hpre : IsCompact ((coulombGroundStateL2 hβ) ⁻¹' K) :=
    (coulombGroundStateL2 hβ).isometry.isClosedEmbedding.isCompact_preimage hK
  apply hpre.closure_of_subset
  rintro _ ⟨u, hu, rfl⟩
  change ‖u‖ ≤ R at hu
  change coulombGroundStateL2 hβ (coulombFormValueL N hβ u) ∈ K
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation N hβ u
  have hlim := ((coulombGroundStateL2 hβ).continuous.tendsto
    (coulombFormValueL N hβ u)).comp (((coulombFormValueL N hβ).continuous.tendsto u).comp hφ)
  apply isClosed_closure.mem_of_tendsto hlim
  have he : ∀ᶠ n in atTop, ‖coulombFormCore hβ (φ n)‖ < R + 1 :=
    hφ.norm.eventually (gt_mem_nhds (by linarith : ‖u‖ < R + 1))
  filter_upwards [he] with n hn
  apply subset_closure
  exact ⟨φ n, hn.le, (coulombGroundStateL2_core hβ (φ n)).symm⟩

end RepulsiveCoulomb
