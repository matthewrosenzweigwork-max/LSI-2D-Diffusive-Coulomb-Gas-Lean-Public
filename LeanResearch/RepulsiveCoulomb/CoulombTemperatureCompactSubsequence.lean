module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateIntervalCompactness

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. One shared subsequence for temperature
and actual normalized core ground states in the fixed ambient volume L2. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombTemperature_groundState_subsequence {N : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (β : ℕ → ℝ)
    (hβ : ∀ n, β n ∈ Set.Icc a b) (R : ℝ)
    (φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤)
    (hφ : ∀ n, ‖coulombFormCore (ha.trans_le (hβ n).1) (φ n)‖ ≤ R) :
    ∃ βstar ∈ Set.Icc a b, ∃ ψ : Lp ℝ 2 (volume : Measure (CoulombConfig N)),
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (β ∘ σ) atTop (𝓝 βstar) ∧
      Tendsto (fun n => coulombGroundStateCoreLp (ha.trans_le (hβ (σ n)).1) (φ (σ n)))
        atTop (𝓝 ψ) := by
  let i : ℕ → CoulombIntervalCore N a b R ha := fun n =>
    ⟨⟨β n, hβ n⟩, ⟨φ n, hφ n⟩⟩
  let x : ℕ → ℝ × Lp ℝ 2 (volume : Measure (CoulombConfig N)) :=
    fun n => (β n, coulombIntervalGroundStateLp N a b R ha (i n))
  have hK := coulombIntervalGroundState_compact N a b R ha hab
  have hc := (isCompact_Icc : IsCompact (Set.Icc a b)).prod hK
  have hx (n : ℕ) : x n ∈ Set.Icc a b ×ˢ
      closure (range (coulombIntervalGroundStateLp N a b R ha)) :=
    ⟨hβ n, subset_closure (mem_range_self (i n))⟩
  obtain ⟨p, hp, σ, hσ, ht⟩ := hc.tendsto_subseq hx
  refine ⟨p.1, hp.1, p.2, σ, hσ, ?_, ?_⟩
  · simpa only [x, Function.comp_def] using ht.fst_nhds
  · simpa only [x, i, coulombIntervalGroundStateLp, Function.comp_def] using ht.snd_nhds

end RepulsiveCoulomb
