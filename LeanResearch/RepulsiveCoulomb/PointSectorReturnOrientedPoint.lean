import LeanResearch.RepulsiveCoulomb.PointSectorReturnBoundaryClock

/-! Isolated, uncompiled topological endpoint form of the actual boundary
clock constructor. Its return point is genuinely outside the old metric ray;
both parameter orientations are handled internally. -/
noncomputable section
open Set
open scoped NNReal
namespace RepulsiveCoulomb

theorem exists_clean_ray_oriented_boundary_to_external_point
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (ρ : ℝ → ℂ)
    (hρd : ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v)
    (hρfront : ∀ u ∈ Ici (0 : ℝ), ρ u ∈ frontier P)
    {q : ℂ} (hw : q ∈ frontier P)
    (hq : ∀ T ∈ Ici (0 : ℝ), q ≠ ρ T) :
    ∃ b : ℝ → ℂ, Continuous b ∧ Function.Injective b ∧ range b = frontier P ∧
      ∃ s t : ℝ, s < t ∧ b s = ρ 0 ∧ b t = q ∧
        ∀ v : ℝ, 0 < v → ∃ u < s, b u = ρ v := by
  let ρN : ℝ≥0 → ℂ := fun u => ρ u
  have hρNmetric : ∀ u v : ℝ≥0,
      (pointSmoothConformalEDist a y (ρN u) (ρN v)).toReal = dist u v := by
    intro u v
    change (pointSmoothConformalEDist a y (ρ (u : ℝ)) (ρ (v : ℝ))).toReal =
      dist (u : ℝ) (v : ℝ)
    exact hρd u u.prop v v.prop
  have hρN := pointMetricRay_isClosedEmbedding ha y ρN hρNmetric
  obtain ⟨b, hb, hbi, hboundary, f, hf, hρf⟩ :=
    straightened_halfplane_actual_boundary_clock H hP ρN hρN.continuous
      (fun u => hρfront u u.prop)
  let s := f 0
  have hs : b s = ρ 0 := (hρf 0).symm
  obtain ⟨t, ht⟩ := hboundary.symm ▸ hw
  have hst : s ≠ t := by
    intro he
    have hpq : q = ρ 0 := ht.symm.trans (he ▸ hs)
    exact hq 0 (show (0 : ℝ) ≤ 0 from le_rfl) hpq
  have hbaseClock (u : ℝ≥0) (hu : 0 < u) : f u ≠ s := by
    intro he
    have heρ : ρN u = ρN 0 := (hρf u).trans ((congrArg b he).trans (hρf 0).symm)
    exact hu.ne' (hρN.injective heρ)
  have hreturnClock (u : ℝ≥0) : f u ≠ t := by
    intro he
    have heρ : q = ρ (u : ℝ) := ht.symm.trans ((congrArg b he).symm.trans (hρf u).symm)
    exact hq u u.prop heρ
  have hescape : ∀ K : Set ℂ, IsCompact K → ∃ u : ℝ≥0, 0 < u ∧ ρN u ∉ K :=
    fun K hK => nnreal_closedEmbedding_positive_escape hρN hK
  rcases escaping_boundary_clock_opposite_return b hb ρN f hf hρf hst rfl
      hbaseClock hreturnClock hescape with ⟨hst, hlow⟩ | ⟨hts, hhigh⟩
  · refine ⟨b, hb, hbi, hboundary, s, t, hst, hs, ht, ?_⟩
    intro v hv
    let u : ℝ≥0 := ⟨v, hv.le⟩
    have hu : 0 < u := by exact_mod_cast hv
    exact ⟨f u, hlow u hu, (hρf u).symm⟩
  · let b' : ℝ → ℂ := fun u => b (-u)
    have hb' : Continuous b' := hb.comp continuous_neg
    have hbi' : Function.Injective b' := hbi.comp neg_injective
    have hboundary' : range b' = frontier P := by
      rw [← hboundary]
      ext x
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨-u, hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨-u, by simpa only [b', neg_neg] using hu⟩
    refine ⟨b', hb', hbi', hboundary', -s, -t, by linarith, ?_, ?_, ?_⟩
    · simpa only [b', neg_neg] using hs
    · simpa only [b', neg_neg] using ht
    · intro v hv
      let u : ℝ≥0 := ⟨v, hv.le⟩
      have hu : 0 < u := by exact_mod_cast hv
      refine ⟨-f u, by have h := hhigh u hu; linarith, ?_⟩
      change b (-(-f u)) = ρN u
      simpa only [neg_neg] using (hρf u).symm

end RepulsiveCoulomb
