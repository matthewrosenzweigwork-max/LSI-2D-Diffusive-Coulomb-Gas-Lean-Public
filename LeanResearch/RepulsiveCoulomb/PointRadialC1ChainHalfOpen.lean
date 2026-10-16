import LeanResearch.RepulsiveCoulomb.PointGeodesicFiniteRadialC1Chain

/-! Actual half-open joint injectivity of macro-arcs follows from the source
interval order. Both half-open conventions are retained for the reversed
second side of a cyclic bigon. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
namespace PointRadialC1ArcPiece
variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
  {γ : Icc (0 : ℝ) 1 → ℂ}

theorem halfOpen_image (e : PointRadialC1ArcPiece ha y γ) (hi : Function.Injective γ) :
    e.curve '' Ico (0 : ℝ) 1 = γ '' Ico e.start e.finish := by
  apply Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    have hmem : e.curve u ∈ e.curve '' Icc (0 : ℝ) 1 := ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩
    rw [e.image] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    have hvf : v ≠ e.finish := by
      intro he
      have hu1 := e.injective ⟨hu.1, hu.2.le⟩ (by norm_num)
        (hvu.symm.trans ((congrArg γ he).trans e.at_one.symm))
      exact hu.2.ne hu1
    exact ⟨v, ⟨hv.1, lt_of_le_of_ne hv.2 hvf⟩, hvu⟩
  · rintro z ⟨v, hv, rfl⟩
    have hmem : γ v ∈ e.curve '' Icc (0 : ℝ) 1 := by
      rw [e.image]
      exact ⟨v, ⟨hv.1, hv.2.le⟩, rfl⟩
    obtain ⟨u, hu, huv⟩ := hmem
    have hu1 : u ≠ 1 := by
      intro he
      rw [he, e.at_one] at huv
      exact hv.2.ne (hi huv).symm
    exact ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2 hu1⟩, huv⟩

theorem reverseHalfOpen_image (e : PointRadialC1ArcPiece ha y γ) (hi : Function.Injective γ) :
    e.curve '' Ioc (0 : ℝ) 1 = γ '' Ioc e.start e.finish := by
  apply Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    have hmem : e.curve u ∈ e.curve '' Icc (0 : ℝ) 1 := ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩
    rw [e.image] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    have hvs : v ≠ e.start := by
      intro he
      have hu0 := e.injective ⟨hu.1.le, hu.2⟩ (by norm_num)
        (hvu.symm.trans ((congrArg γ he).trans e.at_zero.symm))
      exact hu.1.ne' hu0
    exact ⟨v, ⟨lt_of_le_of_ne hv.1 (Ne.symm hvs), hv.2⟩, hvu⟩
  · rintro z ⟨v, hv, rfl⟩
    have hmem : γ v ∈ e.curve '' Icc (0 : ℝ) 1 := by
      rw [e.image]
      exact ⟨v, ⟨hv.1.le, hv.2⟩, rfl⟩
    obtain ⟨u, hu, huv⟩ := hmem
    have hu0 : u ≠ 0 := by
      intro he
      rw [he, e.at_zero] at huv
      exact hv.1.ne (hi huv)
    exact ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩, huv⟩

end PointRadialC1ArcPiece
namespace PointRadialC1ArcChain
variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
  {γ : Icc (0 : ℝ) 1 → ℂ}

theorem halfOpen_pairwise_disjoint {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) {e f : PointRadialC1ArcPiece ha y γ}
    (he : e ∈ es) (hf : f ∈ es) (hef : e ≠ f) :
    Disjoint (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1) := by
  rw [e.halfOpen_image hi, f.halfOpen_image hi]
  apply disjoint_left.mpr
  rintro z ⟨u, hu, huz⟩ ⟨v, hv, hvz⟩
  have huv := hi (huz.trans hvz.symm)
  subst v
  rcases h.pair_order e he f hf hef with hef | hfe
  · exact (not_le.mpr hu.2) (hef.trans hv.1)
  · exact (not_le.mpr hv.2) (hfe.trans hu.1)

theorem reverseHalfOpen_pairwise_disjoint {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) {e f : PointRadialC1ArcPiece ha y γ}
    (he : e ∈ es) (hf : f ∈ es) (hef : e ≠ f) :
    Disjoint (e.curve '' Ioc (0 : ℝ) 1) (f.curve '' Ioc (0 : ℝ) 1) := by
  rw [e.reverseHalfOpen_image hi, f.reverseHalfOpen_image hi]
  apply disjoint_left.mpr
  rintro z ⟨u, hu, huz⟩ ⟨v, hv, hvz⟩
  have huv := hi (huz.trans hvz.symm)
  subst v
  rcases h.pair_order e he f hf hef with hef | hfe
  · exact (not_le.mpr hv.1) (hu.2.trans hef)
  · exact (not_le.mpr hu.1) (hv.2.trans hfe)

theorem halfOpen_joint_injective {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) {e f : PointRadialC1ArcPiece ha y γ}
    (he : e ∈ es) (hf : f ∈ es) {u v : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) (hv : v ∈ Ico (0 : ℝ) 1) (heq : e.curve u = f.curve v) :
    e = f ∧ u = v := by
  by_cases hef : e = f
  · subst f
    exact ⟨rfl, e.injective ⟨hu.1, hu.2.le⟩ ⟨hv.1, hv.2.le⟩ heq⟩
  · exact (disjoint_left.mp (h.halfOpen_pairwise_disjoint hi he hf hef)
      ⟨u, hu, rfl⟩ ⟨v, hv, heq.symm⟩).elim

theorem halfOpen_subset_total {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) {e : PointRadialC1ArcPiece ha y γ} (he : e ∈ es) :
    e.curve '' Ico (0 : ℝ) 1 ⊆ γ '' Ico s t := by
  rw [e.halfOpen_image hi]
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨hs, ht⟩ := h.piece_bounds he
  exact ⟨u, ⟨hs.trans hu.1, hu.2.trans_le ht⟩, rfl⟩

theorem reverseHalfOpen_subset_total {s t : Icc (0 : ℝ) 1}
    {es : List (PointRadialC1ArcPiece ha y γ)} (h : PointRadialC1ArcChain ha y γ s t es)
    (hi : Function.Injective γ) {e : PointRadialC1ArcPiece ha y γ} (he : e ∈ es) :
    e.curve '' Ioc (0 : ℝ) 1 ⊆ γ '' Ioc s t := by
  rw [e.reverseHalfOpen_image hi]
  rintro z ⟨u, hu, rfl⟩
  obtain ⟨hs, ht⟩ := h.piece_bounds he
  exact ⟨u, ⟨hs.trans_lt hu.1, hu.2.trans ht⟩, rfl⟩

end PointRadialC1ArcChain
end RepulsiveCoulomb
