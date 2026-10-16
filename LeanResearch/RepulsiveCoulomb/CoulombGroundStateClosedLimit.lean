module

public import LeanResearch.RepulsiveCoulomb.CoulombFormApproximation
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateL2

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. Recover a genuine fixed-temperature
closed-form element from a convergent ground-state sequence and vanishing
physical gradients. Surjectivity of the ground-state isometry is not assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombGroundState_closed_zero_gradient_limit {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (u : ℕ → CoulombFormDomain N hβ)
    (ψ : Lp ℝ 2 (volume : Measure (CoulombConfig N)))
    (hψ : Tendsto (fun n => coulombGroundStateL2 hβ (coulombFormValueL N hβ (u n)))
      atTop (𝓝 ψ))
    (hg : Tendsto (fun n => coulombFormGradientL N hβ (u n)) atTop (𝓝 0)) :
    ∃ v : CoulombFormDomain N hβ,
      coulombGroundStateL2 hβ (coulombFormValueL N hβ v) = ψ ∧
      coulombFormGradientL N hβ v = 0 ∧ Tendsto u atTop (𝓝 v) := by
  have hclosed := (coulombGroundStateL2 (N := N) hβ).isometry.isClosedEmbedding.isClosed_range
  have hmem := hclosed.mem_of_tendsto hψ
    (Eventually.of_forall fun n => mem_range_self (coulombFormValueL N hβ (u n)))
  obtain ⟨f, hf⟩ := hmem
  have hv : Tendsto (fun n => coulombFormValueL N hβ (u n)) atTop (𝓝 f) := by
    apply (coulombGroundStateL2 hβ).isometry.isEmbedding.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, hf] using hψ
  have hpair : Tendsto (fun n => coulombFormGraphL N hβ (u n)) atTop (𝓝 (f, 0)) :=
    hv.prodMk_nhds hg
  have hp := (coulombFormGraphL_closed_range N hβ).mem_of_tendsto hpair
    (Eventually.of_forall fun n => mem_range_self (u n))
  obtain ⟨v, hvgraph⟩ := hp
  have hvalue : coulombFormValueL N hβ v = f := congrArg Prod.fst hvgraph
  have hzero : coulombFormGradientL N hβ v = 0 := congrArg Prod.snd hvgraph
  have he := (coulombFormGraphL_antilipschitz N hβ).isEmbedding
    (coulombFormGraphL N hβ).continuous
  refine ⟨v, by rw [hvalue]; exact hf, hzero, he.tendsto_nhds_iff.mpr ?_⟩
  simpa only [hvgraph, Function.comp_def] using! hpair

end RepulsiveCoulomb
