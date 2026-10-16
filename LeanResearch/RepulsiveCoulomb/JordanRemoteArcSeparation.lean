import LeanResearch.RepulsiveCoulomb.JordanDisjointCornerNeighborhoods

/-! Actual compact separation of all nonlocal pieces from a chosen corner of
a simple closed parametrized loop. Instantiating the finite neighborhood
construction with these complements makes every small chart image meet only
the prescribed local parameter window, rather than assuming this separation.
Records-only candidate. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The remote part of an actual simple closed loop is compact and misses
an interior parameter point. Its complement is a constructed neighborhood
whose boundary hits necessarily have parameters in the prescribed window. -/
theorem exists_corner_neighborhood_excluding_remote_arcs
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hclose : γ 1 = γ 0)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {c a : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : 0 < a) :
    ∃ U : Set ℂ, IsOpen U ∧ γ c ∈ U ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U → t ∈ Ioo (c - a) (c + a) := by
  let K := γ '' (Icc (0 : ℝ) (c - a) ∪ Icc (c + a) 1)
  have hK : IsCompact K := (isCompact_Icc.union isCompact_Icc).image hγ
  have hpK : γ c ∉ K := by
    rintro ⟨t, ht, heq⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rcases ht with ht | ht
      · exact ⟨ht.1, by linarith [ht.2, hc.2]⟩
      · exact ⟨by linarith [ht.1, hc.1], ht.2⟩
    have htc : t ≠ c := by
      intro h
      subst t
      rcases ht with ht | ht <;> linarith [ht.1, ht.2]
    by_cases ht1 : t = 1
    · subst t
      have he : γ c = γ 0 := heq.symm.trans hclose
      have hz := hinj ⟨hc.1.le, hc.2⟩ (by norm_num : (0 : ℝ) ∈ Ico 0 1) he
      linarith [hc.1]
    · exact htc (hinj ⟨htI.1, lt_of_le_of_ne htI.2 ht1⟩ ⟨hc.1.le, hc.2⟩ heq)
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hpK, ?_⟩
  intro t ht hremote
  constructor
  · by_contra hn
    exact hremote ⟨t, Or.inl ⟨ht.1, le_of_not_gt hn⟩, rfl⟩
  · by_contra hn
    exact hremote ⟨t, Or.inr ⟨le_of_not_gt hn, ht.2⟩, rfl⟩

/-- For a finite actual corner family, uniformly small disjoint chart images
avoid the chosen off-curve point and every remote part of the actual loop.
All physical neighborhoods and positive radii are constructed. -/
theorem exists_finite_chart_disks_meeting_only_local_arcs
    {ι : Type*} [Finite ι] {γ : ℝ → ℂ}
    (hγ : Continuous γ) (hclose : γ 1 = γ 0) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (c a : ι → ℝ) (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1)
    (hcj : Function.Injective c) (ha : ∀ i, 0 < a i)
    (w : ℂ) (hw : w ∉ γ '' Icc (0 : ℝ) 1)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (hH : ∀ i, ContinuousOn (H i) (V i))
    (hH0 : ∀ i, H i 0 = γ (c i)) :
    ∃ R ρ : ℝ, 0 < R ∧ 0 < ρ ∧ ρ < R ∧
      (∀ i, closedBall (0 : ℂ) R ⊆ V i) ∧
      (∀ i, w ∉ H i '' closedBall (0 : ℂ) R) ∧
      Pairwise (fun i j => Disjoint
        (H i '' closedBall (0 : ℂ) R) (H j '' closedBall (0 : ℂ) R)) ∧
      ∀ i t, t ∈ Icc (0 : ℝ) 1 → γ t ∈ H i '' closedBall (0 : ℂ) R →
        t ∈ Ioo (c i - a i) (c i + a i) := by
  classical
  have hneigh (i : ι) := exists_corner_neighborhood_excluding_remote_arcs hγ hclose hinj (hc i) (ha i)
  choose U hU hpU hlocal using hneigh
  have hp : Function.Injective (fun i => γ (c i)) := by
    intro i j heq
    exact hcj (hinj ⟨(hc i).1.le, (hc i).2⟩ ⟨(hc j).1.le, (hc j).2⟩ heq)
  have hwc (i : ι) : w ≠ γ (c i) := by
    intro heq
    exact hw ⟨c i, Ioo_subset_Icc_self (hc i), heq.symm⟩
  obtain ⟨r, R, ρ, _, hR, hρ, hρR, hrU, _, _, hRV, _, himage, havoid, hdisj⟩ :=
    exists_uniform_disjoint_chart_disks (fun i => γ (c i)) hp w hwc U hU hpU V hV h0V H hH hH0
  refine ⟨R, ρ, hR, hρ, hρR, hRV, havoid, hdisj, ?_⟩
  intro i t ht hmem
  exact hlocal i t ht (hrU i (Metric.ball_subset_closedBall (himage i hmem)))

end RepulsiveCoulomb
