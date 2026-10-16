module

public import LeanResearch.RepulsiveCoulomb.FiniteClosedContactComponents

@[expose] public section

/-! Successor draft. A finite closed order-connected cover of the actual
compact parameter interval produces finitely many transition times. It is not
assumed to be an ordered partition, disjoint cover, or transverse crossing list. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every open gap between the constructed finite set of endpoints lies,
including both endpoints, in a single actual cover interval. Singleton and
empty cover members are allowed and introduce no false positive-length edge. -/
theorem finite_closed_interval_cover_transition_times
    {ι : Type*} [Fintype ι] (J : ι → Set unitInterval)
    (hclosed : ∀ i, IsClosed (J i)) (hinterval : ∀ i, OrdConnected (J i))
    (hcover : ∀ u : unitInterval, ∃ i, u ∈ J i) :
    ∃ P : Finset unitInterval, ∀ s t : unitInterval, s < t →
      (∀ u ∈ Ioo s t, u ∉ P) → ∃ i, Icc s t ⊆ J i := by
  classical
  have hends (i : ι) : ∃ lo hi : unitInterval,
      (J i).Nonempty → IsLeast (J i) lo ∧ IsGreatest (J i) hi := by
    by_cases hn : (J i).Nonempty
    · obtain ⟨lo, hlo⟩ := (hclosed i).isCompact.exists_isLeast hn
      obtain ⟨hi, hhi⟩ := (hclosed i).isCompact.exists_isGreatest hn
      exact ⟨lo, hi, fun _ => ⟨hlo, hhi⟩⟩
    · exact ⟨0, 0, fun h => (hn h).elim⟩
  choose lo hi hends using hends
  let P : Finset unitInterval := Finset.univ.biUnion (fun i => {lo i, hi i})
  refine ⟨P, ?_⟩
  intro s t hst hgap
  let u : unitInterval := ⟨(s.1 + t.1) / 2, by
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩
  have hsu : s < u := by change s.1 < (s.1 + t.1) / 2; linarith [show s.1 < t.1 from hst]
  have hut : u < t := by change (s.1 + t.1) / 2 < t.1; linarith [show s.1 < t.1 from hst]
  obtain ⟨i, hui⟩ := hcover u
  obtain ⟨hlo, hhi⟩ := hends i ⟨u, hui⟩
  have hloP : lo i ∈ P := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp⟩
  have hhiP : hi i ∈ P := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp⟩
  have hlos : lo i ≤ s := by
    by_contra h
    exact hgap (lo i) ⟨lt_of_not_ge h, (hlo.2 hui).trans_lt hut⟩ hloP
  have hthi : t ≤ hi i := by
    by_contra h
    exact hgap (hi i) ⟨hsu.trans_le (hhi.2 hui), lt_of_not_ge h⟩ hhiP
  refine ⟨i, ?_⟩
  intro v hv
  exact (hinterval i).out hlo.1 hhi.1 ⟨hlos.trans hv.1, hv.2.trans hthi⟩

end RepulsiveCoulomb
