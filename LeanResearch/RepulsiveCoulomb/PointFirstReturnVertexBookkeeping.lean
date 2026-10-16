module

public import LeanResearch.RepulsiveCoulomb.PointFirstReturnInternalNewTurns

@[expose] public section

/-! Successor draft. Identify the two actual contact points as unique vertices
of the constructed positive family, and identify all other old-frontier
vertices with the unchanged old arc off the stopped ray. No endpoint-slot or
old/new vertex classification certificate is supplied. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A point on a closed finite-family carrier that is in no open edge must be
an actual vertex. Terminal endpoints are reassigned using the proved joins. -/
theorem finite_closed_family_vertex_of_no_open_edge
    (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    {p : ℂ} (hp : p ∈ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)
    (hno : ∀ k ≤ n, ∀ u ∈ Ioo (0 : ℝ) 1, f k u ≠ p) :
    ∃ k ≤ n, f k 0 = p := by
  obtain ⟨k, hp⟩ := mem_iUnion.mp hp
  obtain ⟨hk, u, hu, hup⟩ := mem_iUnion.mp hp
  by_cases hu0 : u = 0
  · exact ⟨k, hk, by simpa only [hu0] using hup⟩
  by_cases hu1 : u = 1
  · have hp1 : f k 1 = p := by simpa only [hu1] using hup
    by_cases hkn : k = n
    · exact ⟨0, Nat.zero_le n, hclose.symm.trans (hkn ▸ hp1)⟩
    · have hlt : k < n := lt_of_le_of_ne hk hkn
      exact ⟨k + 1, by omega, (hv k hlt).symm.trans hp1⟩
  · exact False.elim (hno k hk u
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩ hup)

/-- Both old-arc and stopped-ray half-open ownership laws exclude the actual
initial and far contacts from every open macro-edge of the assembled list. -/
theorem firstReturn_source_endpoints_not_on_open_edges
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (β γ : unitInterval → ℂ) (hβi : Function.Injective β) (hγi : Function.Injective γ)
    (h0 : β 0 = γ 0) (h1 : β 1 = γ 1)
    (old : List (PointRadialC1PlaneArc ha y))
    (hold : PointBoundaryRadialChainOn ha y β 0 1 old)
    (fresh : List (PointRadialC1ArcPiece ha y γ))
    (hfresh : PointRadialC1ArcChain ha y γ 0 1 fresh) :
    let L := old ++ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
    ∀ e ∈ L, ∀ u ∈ Ioo (0 : ℝ) 1, e.curve u ≠ γ 0 ∧ e.curve u ≠ γ 1 := by
  intro L e he u hu
  rcases List.mem_append.mp he with he | he
  · constructor
    · intro heq
      obtain ⟨v, hv, hvu⟩ := hold.reverseHalfOpen e he ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩
      have hv0 : v = 0 := hβi ((hvu.trans heq).trans h0.symm)
      exact hv.1.ne' hv0
    · intro heq
      obtain ⟨v, hv, hvu⟩ := hold.halfOpen e he ⟨u, ⟨hu.1.le, hu.2⟩, rfl⟩
      have hv1 : v = 1 := hβi ((hvu.trans heq).trans h1.symm)
      exact hv.2.ne hv1
  · obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
    have hu' : 1 - u ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
    constructor
    · intro heq
      obtain ⟨v, hv, hvu⟩ := hfresh.reverseHalfOpen_subset_total hγi he₀
        ⟨1 - u, ⟨hu'.1, hu'.2.le⟩, rfl⟩
      have hv0 : v = 0 := hγi (hvu.trans heq)
      exact hv.1.ne' hv0
    · intro heq
      obtain ⟨v, hv, hvu⟩ := hfresh.halfOpen_subset_total hγi he₀
        ⟨1 - u, ⟨hu'.1.le, hu'.2⟩, rfl⟩
      have hv1 : v = 1 := hγi (hvu.trans heq)
      exact hv.2.ne hv1

/-- The two source contact points are genuine UNIQUE vertices of the positive
family, irrespective of which literal traversal the orientation theorem chose. -/
theorem PointFirstReturnFiniteGBData.source_contact_vertices
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {U V : Set ℂ} (β γ : unitInterval → ℂ)
    (hβi : Function.Injective β) (hγi : Function.Injective γ)
    (h0 : β 0 = γ 0) (h1 : β 1 = γ 1)
    (old : List (PointRadialC1PlaneArc ha y))
    (hold : PointBoundaryRadialChainOn ha y β 0 1 old)
    (fresh : List (PointRadialC1ArcPiece ha y γ))
    (hfresh : PointRadialC1ArcChain ha y γ 0 1 fresh)
    {n : ℕ} {arcs : ℕ → PointRadialC1PlaneArc ha y}
    (hmem : ∀ k, arcs k ∈ old ++
      ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse)
    (hcarrier : (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) = range γ ∪ range β)
    (D : PointFirstReturnFiniteGBData ha y arcs n U V) :
    ∃ start far : ℕ, start ≤ n ∧ far ≤ n ∧ start ≠ far ∧
      (D.oriented start).curve 0 = γ 0 ∧ (D.oriented far).curve 0 = γ 1 ∧
      (∀ k ≤ n, (D.oriented k).curve 0 = γ 0 → k = start) ∧
      (∀ k ≤ n, (D.oriented k).curve 0 = γ 1 → k = far) := by
  have hno := firstReturn_source_endpoints_not_on_open_edges β γ hβi hγi h0 h1 old hold fresh hfresh
  have hnoB (k : ℕ) (_ : k ≤ n) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      (D.oriented k).curve u ≠ γ 0 ∧ (D.oriented k).curve u ≠ γ 1 := by
    rcases D.orientation with heq | heq
    · simpa only [heq] using hno _ (hmem k) u hu
    · simpa only [heq, PointRadialC1PlaneArc.reverse] using hno _ (hmem (n - k)) (1 - u)
        (by constructor <;> linarith [hu.1, hu.2])
  have hstart : γ 0 ∈ ⋃ k ≤ n, (D.oriented k).curve '' Icc (0 : ℝ) 1 := by
    rw [D.carrier, hcarrier]
    exact Or.inl (mem_range_self 0)
  have hfar : γ 1 ∈ ⋃ k ≤ n, (D.oriented k).curve '' Icc (0 : ℝ) 1 := by
    rw [D.carrier, hcarrier]
    exact Or.inl (mem_range_self 1)
  obtain ⟨start, hs, hs0⟩ := finite_closed_family_vertex_of_no_open_edge _ n
    D.consecutive D.closing hstart (fun k hk u hu => (hnoB k hk u hu).1)
  obtain ⟨far, hf, hf0⟩ := finite_closed_family_vertex_of_no_open_edge _ n
    D.consecutive D.closing hfar (fun k hk u hu => (hnoB k hk u hu).2)
  have hne : start ≠ far := by
    intro he
    have hpoints : γ 0 = γ 1 := by rw [← hs0, ← hf0, he]
    have hc : (0 : unitInterval) = 1 := hγi hpoints
    norm_num at hc
  refine ⟨start, far, hs, hf, hne, hs0, hf0, ?_, ?_⟩
  · intro k hk he
    exact (D.simple k start hk hs 0 0 (by norm_num) (by norm_num) (he.trans hs0.symm)).1
  · intro k hk he
    exact (D.simple k far hk hf 0 0 (by norm_num) (by norm_num) (he.trans hf0.symm)).1

/-- Every old-frontier point of the cap except the two contacts is on the
unchanged old arc and off the entire stopped ray. This is the precise input
needed by the derived old-region germ equality and retained-width comparison. -/
theorem firstReturn_other_boundary_vertex_on_old_arc
    {P : Set ℂ} {r b : ℝ → ℂ} {z w s t : ℝ} (hzw : z < w)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P)
    {p : ℂ} (hp : p ∈ range (lineCapSegment r z w) ∪ range (lineCapSegment b s t))
    (hpP : p ∈ frontier P) (hpz : p ≠ r z) (hpw : p ≠ r w) :
    p ∈ range (lineCapSegment b s t) ∧ p ∉ range (lineCapSegment r z w) := by
  have hnot : p ∉ range (lineCapSegment r z w) := by
    intro hnew
    rw [lineCapSegment_range r hzw] at hnew
    obtain ⟨u, hu, hup⟩ := hnew
    have huz : u ≠ z := fun he => hpz (hup.symm.trans (congrArg r he))
    have huw : u ≠ w := fun he => hpw (hup.symm.trans (congrArg r he))
    exact hgap u ⟨lt_of_le_of_ne hu.1 (Ne.symm huz), lt_of_le_of_ne hu.2 huw⟩ (hup.symm ▸ hpP)
  exact ⟨hp.resolve_left hnot, hnot⟩

/-- Source-coordinate exclusion of the original base implies literal old-arc
omission. This is an ordinary order/geometric fact, not a signed-mass premise. -/
theorem lineCapSegment_avoids_old_base
    {b : ℝ → ℂ} (hbi : Function.Injective b) {s t q : ℝ}
    (hq : q ∉ uIcc s t) : b q ∉ range (lineCapSegment b s t) := by
  rintro ⟨u, hu⟩
  have heq : s + u.1 * (t - s) = q := hbi hu
  apply hq
  rw [← heq]
  rcases le_total s t with hst | hts
  · rw [uIcc_of_le hst]
    constructor <;> nlinarith [u.2.1, u.2.2]
  · rw [uIcc_of_ge hts]
    constructor <;> nlinarith [u.2.1, u.2.2]

end RepulsiveCoulomb
