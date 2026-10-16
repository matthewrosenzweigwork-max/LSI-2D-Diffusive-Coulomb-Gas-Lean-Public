import LeanResearch.RepulsiveCoulomb.ProperBoundaryClockArclength
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-! SOURCE-ONLY, UNCOMPILED. One-sided arclength from a proper topological
clock. Only positive-clock subarcs are required to contain minimizing segments.
Continuity supplies the initial endpoint; no metric regularity there is assumed. -/
noncomputable section
open Set Topology
namespace ProperBoundaryEndClock
variable {X : Type*} [MetricSpace X]

/-- A minimizing chord in an embedded real clock cannot leave the interval
between its endpoint clocks. This is topology plus injectivity of the chord,
not geodesic uniqueness in the ambient metric space. -/
theorem minimizing_chord_mem_clock_interval
    {β : ℝ → X} (hβ : IsEmbedding β) {s t : ℝ}
    (γ : unitInterval → X) (hc : Continuous γ)
    (h0 : γ 0 = β s) (h1 : γ 1 = β t)
    (hrange : range γ ⊆ range β)
    (hd : ∀ u v, dist (γ u) (γ v) = |(u : ℝ) - (v : ℝ)| * dist (β s) (β t)) :
    range γ ⊆ β '' uIcc s t := by
  let e : ℝ ≃ₜ range β := hβ.toHomeomorph
  let γr : unitInterval → range β := fun v => ⟨γ v, hrange ⟨v, rfl⟩⟩
  let δ : unitInterval → ℝ := fun v => e.symm (γr v)
  have hδc : Continuous δ := e.symm.continuous.comp
    (hc.subtype_mk (fun v => hrange ⟨v, rfl⟩))
  have hβδ (v : unitInterval) : β (δ v) = γ v :=
    congrArg Subtype.val (e.apply_symm_apply (γr v))
  have hδ0 : δ 0 = s := hβ.injective (by rw [hβδ, h0])
  have hδ1 : δ 1 = t := hβ.injective (by rw [hβδ, h1])
  by_cases hst : s = t
  · rintro x ⟨v, rfl⟩
    have he : γ v = β s := by
      apply dist_eq_zero.mp
      rw [← h0, hd, hst, dist_self, mul_zero]
    exact ⟨s, by simp [hst], he.symm⟩
  have hD : dist (β s) (β t) ≠ 0 := dist_ne_zero.mpr (hβ.injective.ne hst)
  have hδi : Function.Injective δ := by
    intro u v huv
    have hγ : γ u = γ v := by rw [← hβδ, ← hβδ, huv]
    have hz : |(u : ℝ) - (v : ℝ)| = 0 := by
      have h := hd u v
      rw [hγ, dist_self] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hD
    exact Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp hz))
  rintro x ⟨v, rfl⟩
  refine ⟨δ v, ?_, hβδ v⟩
  rcases hδc.strictMono_of_inj hδi with hm | hm
  · have hleft := hm.monotone (show (0 : unitInterval) ≤ v from v.2.1)
    have hright := hm.monotone (show v ≤ (1 : unitInterval) from v.2.2)
    rw [hδ0] at hleft
    rw [hδ1] at hright
    exact mem_uIcc_of_le hleft hright
  · have hleft := hm.antitone (show (0 : unitInterval) ≤ v from v.2.1)
    have hright := hm.antitone (show v ≤ (1 : unitInterval) from v.2.2)
    rw [hδ0] at hleft
    rw [hδ1] at hright
    exact mem_uIcc_of_ge hright hleft

/-- Only a segment with the two outside endpoints is needed for order
additivity at an intermediate clock point. -/
theorem dist_additive_of_one_contained_segment
    {β : ℝ → X} (hβ : IsEmbedding β) {s t u : ℝ}
    (hst : s ≤ t) (htu : t ≤ u)
    (γ : unitInterval → X) (hc : Continuous γ)
    (h0 : γ 0 = β s) (h1 : γ 1 = β u)
    (hrange : range γ ⊆ range β)
    (hd : ∀ v w, dist (γ v) (γ w) = |(v : ℝ) - (w : ℝ)| * dist (β s) (β u)) :
    dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u) := by
  let e : ℝ ≃ₜ range β := hβ.toHomeomorph
  let γr : unitInterval → range β := fun v => ⟨γ v, hrange ⟨v, rfl⟩⟩
  let δ : unitInterval → ℝ := fun v => e.symm (γr v)
  have hδc : Continuous δ := e.symm.continuous.comp
    (hc.subtype_mk (fun v => hrange ⟨v, rfl⟩))
  have hβδ (v : unitInterval) : β (δ v) = γ v :=
    congrArg Subtype.val (e.apply_symm_apply (γr v))
  have hδ0 : δ 0 = s := hβ.injective (by rw [hβδ, h0])
  have hδ1 : δ 1 = u := hβ.injective (by rw [hβδ, h1])
  have ht : t ∈ Icc (δ 0) (δ 1) := by rw [hδ0, hδ1]; exact ⟨hst, htu⟩
  obtain ⟨v, hv⟩ := intermediate_value_univ
    (0 : unitInterval) (1 : unitInterval) hδc ht
  have hvγ : γ v = β t := by rw [← hβδ v, hv]
  have hl := hd (0 : unitInterval) v
  have hr := hd v (1 : unitInterval)
  simp [h0, hvγ, abs_of_nonneg v.2.1] at hl
  simp [hvγ, h1, abs_of_nonpos (sub_nonpos.mpr v.2.2)] at hr
  nlinarith

/-- Continuity adds the possibly singular initial endpoint to positive-clock
order additivity. It does not identify the two sides of a corner. -/
theorem dist_additive_nonnegative_of_positive
    {β : ℝ → X} (hc : Continuous β)
    (hadd : ∀ s t u : ℝ, 0 < s → s ≤ t → t ≤ u →
      dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u))
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htu : t ≤ u) :
    dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u) := by
  rcases eq_or_lt_of_le hs with hzero | hpos
  · subst s
    by_cases ht : t = 0
    · simp [ht]
    have htpos : 0 < t := lt_of_le_of_ne hst (Ne.symm ht)
    have heq : EqOn (fun v : ℝ => dist (β v) (β u))
        (fun v : ℝ => dist (β v) (β t) + dist (β t) (β u)) (Ioo 0 t) :=
      fun v hv => hadd v t u hv.1 hv.2.le htu
    apply heq.closure (hc.dist continuous_const)
      ((hc.dist continuous_const).add continuous_const)
    rw [closure_Ioo htpos.ne]
    exact ⟨le_rfl, htpos.le⟩
  · exact hadd s t u hpos hst htu

/-- Properness and IVT make unsigned distance from the endpoint onto NNReal.
The full clock is topological; this lemma does not assume distance additivity. -/
theorem radialDistance_surjective [ProperSpace X]
    {β : ℝ → X} (hβ : IsClosedEmbedding β) :
    Function.Surjective (fun t : NNReal => (⟨dist (β 0) (β t), dist_nonneg⟩ : NNReal)) := by
  intro r
  obtain ⟨t, ht, hfar⟩ := ProperBoundaryClock.exists_positive_far_point hβ (r : ℝ)
  have hc : Continuous (fun u : ℝ => dist (β 0) (β u)) :=
    continuous_const.dist hβ.continuous
  have hr : (r : ℝ) ∈ Icc (dist (β 0) (β 0)) (dist (β 0) (β t)) := by
    simpa only [dist_self, mem_Icc] using And.intro r.2 hfar.le
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc ht.le hc.continuousOn hr
  exact ⟨⟨u, hu.1⟩, Subtype.ext hur⟩

/-- A proper topological half-end with positively ordered minimizing arcs has
a genuine complete NNReal metric parametrization, including its initial
endpoint and its entire half-end range. -/
theorem exists_isometry_of_positive_additivity [ProperSpace X]
    {β : ℝ → X} (hβ : IsClosedEmbedding β)
    (hadd : ∀ s t u : ℝ, 0 < s → s ≤ t → t ≤ u →
      dist (β s) (β u) = dist (β s) (β t) + dist (β t) (β u)) :
    ∃ ρ : NNReal → X, Isometry ρ ∧ ρ 0 = β 0 ∧
      range ρ = β '' Ici (0 : ℝ) ∧
      ∀ t : NNReal, ρ ⟨dist (β 0) (β t), dist_nonneg⟩ = β t := by
  let d : NNReal → NNReal := fun t => ⟨dist (β 0) (β t), dist_nonneg⟩
  have hd (s t : NNReal) : dist (d s) (d t) = dist (β s) (β t) := by
    rcases le_total s t with hst | hts
    · have he := dist_additive_nonnegative_of_positive hβ.continuous hadd
        (s := 0) (t := (s : ℝ)) (u := (t : ℝ)) le_rfl s.2 hst
      rw [NNReal.dist_eq, abs_sub_comm]
      change |dist (β 0) (β t) - dist (β 0) (β s)| = _
      rw [he, add_sub_cancel_left, abs_of_nonneg dist_nonneg]
    · have he := dist_additive_nonnegative_of_positive hβ.continuous hadd
        (s := 0) (t := (t : ℝ)) (u := (s : ℝ)) le_rfl t.2 hts
      rw [NNReal.dist_eq]
      change |dist (β 0) (β s) - dist (β 0) (β t)| = _
      rw [he, add_sub_cancel_left, abs_of_nonneg dist_nonneg, dist_comm]
  have hsurj : Function.Surjective d := radialDistance_surjective hβ
  let c : NNReal → NNReal := fun r => Classical.choose (hsurj r)
  have hc (r : NNReal) : d (c r) = r := Classical.choose_spec (hsurj r)
  let ρ : NNReal → X := fun r => β (c r)
  have hiso : Isometry ρ := by
    apply Isometry.of_dist_eq
    intro s t
    change dist (β (c s)) (β (c t)) = dist s t
    rw [← hd, hc, hc]
  have hparam (t : NNReal) : ρ (d t) = β t := by
    apply dist_eq_zero.mp
    change dist (β (c (d t))) (β t) = 0
    rw [← hd, hc, dist_self]
  have hd0 : d 0 = 0 := by
    apply Subtype.ext
    change dist (β 0) (β 0) = 0
    exact dist_self _
  have hzero : ρ 0 = β 0 := by
    simpa only [hd0, NNReal.coe_zero] using hparam 0
  refine ⟨ρ, hiso, hzero, ?_, hparam⟩
  apply Subset.antisymm
  · rintro x ⟨r, rfl⟩
    exact ⟨(c r : ℝ), (c r).2, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨d ⟨t, ht⟩, hparam ⟨t, ht⟩⟩

end ProperBoundaryEndClock
