import LeanResearch.RepulsiveCoulomb.CoulombFormGlobalCompactness

/-! A bounded actual form sequence with gradient tending to zero has a
subsequence converging in the original form norm to a zero-gradient element.
No kernel or Poincare assertion is assumed or concluded. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombForm_subseq_zero_gradient {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : ℕ → CoulombFormDomain N hβ) (R : ℝ) (hb : ∀ n, ‖u n‖ ≤ R)
    (hg : Tendsto (fun n => coulombFormGradientL N hβ (u n)) atTop (𝓝 0)) :
    ∃ v : CoulombFormDomain N hβ, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (u ∘ σ) atTop (𝓝 v) ∧ coulombFormGradientL N hβ v = 0 := by
  have hc := coulombFormValue_global_compact (N := N) hβ R
  obtain ⟨f, hf, σ, hσ, hv⟩ := hc.tendsto_subseq
    (fun n => subset_closure ⟨u n, hb n, rfl⟩)
  have hgs := hg.comp hσ.tendsto_atTop
  have hpair : Tendsto (fun n => coulombFormGraphL N hβ (u (σ n))) atTop (𝓝 (f, 0)) :=
    hv.prodMk_nhds hgs
  have hmem := (coulombFormGraphL_closed_range N hβ).mem_of_tendsto hpair
    (Eventually.of_forall fun n => mem_range_self (u (σ n)))
  obtain ⟨v, hvgraph⟩ := hmem
  have hzero : coulombFormGradientL N hβ v = 0 := congrArg Prod.snd hvgraph
  have he := (coulombFormGraphL_antilipschitz N hβ).isEmbedding
    (coulombFormGraphL N hβ).continuous
  refine ⟨v, σ, hσ, he.tendsto_nhds_iff.mpr ?_, hzero⟩
  simpa only [hvgraph, Function.comp_def] using! hpair

end RepulsiveCoulomb
