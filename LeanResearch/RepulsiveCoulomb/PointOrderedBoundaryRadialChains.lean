import LeanResearch.RepulsiveCoulomb.PointRadialTriangleArgumentTurn
import LeanResearch.RepulsiveCoulomb.PointRadialListSlots

/-! Successor draft, separate from frozen firstReturnCurvature5. Ordered radial
macro-chains on the literal boundary parametrization. Each local chain below
is constructed from an actual metric geodesic with the same oriented trace.
The source metric law is never transferred to a C1 representative's clock. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Actual curve data on an ordered subarc. Both half-open containment laws
are retained, so appending or reversing chains proves simplicity from source
order. This contains no cap, angle, curvature bound, or GB certificate. -/
structure PointBoundaryRadialChainOn {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (b : unitInterval → ℂ)
    (s t : unitInterval) (L : List (PointRadialC1PlaneArc ha y)) : Prop where
  chain : PointRadialC1PlaneChain ha y (b s) (b t) L
  nonempty : L ≠ []
  carrier : pointRadialC1PlaneCarrier L = b '' Icc s t
  simple : L.Pairwise (fun e f => Disjoint
    (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1))
  halfOpen : ∀ e ∈ L, e.curve '' Ico (0 : ℝ) 1 ⊆ b '' Ico s t
  reverseHalfOpen : ∀ e ∈ L, e.curve '' Ioc (0 : ℝ) 1 ⊆ b '' Ioc s t
  argument : ∀ e ∈ L, e.HasArgumentTurn
  avoid : ∀ e ∈ L, ∀ u ∈ Ioo (0 : ℝ) 1, e.curve u ∉ pointPunctures a y

/-- A minimizing subarc is replaced only by its already constructed radial C1
macro-pieces. Exact trace and endpoint orientation suffice to compare the
half-open carriers with an arbitrary continuous boundary parametrization. -/
theorem exists_boundary_radial_chain_of_metric_subarc
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (b : unitInterval → ℂ) (hbi : Function.Injective b)
    {s t : unitInterval} (hst : s < t)
    (γ : unitInterval → ℂ) (h0 : γ 0 = b s) (h1 : γ 1 = b t)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y (b s) (b t)).toReal)
    (himage : range γ = b '' Icc s t) :
    ∃ L : List (PointRadialC1PlaneArc ha y), PointBoundaryRadialChainOn ha y b s t L := by
  have hneq : b s ≠ b t := fun h => hst.ne (hbi h)
  have hγi := pointConformal_geodesic_injective ha y hneq γ hd
  obtain ⟨es, hes, _, hne, _⟩ :=
    exists_pointConformal_finite_radial_C1_arc_chain ha y hneq γ hd
  let L := es.map PointRadialC1ArcPiece.toPlane
  have hI : Icc (0 : unitInterval) 1 = univ := by
    apply eq_univ_of_forall
    exact fun u => u.2
  have hcarrier : pointRadialC1PlaneCarrier L = b '' Icc s t := by
    rw [hes.toPlane_carrier (by norm_num)]
    change γ '' Icc (0 : unitInterval) 1 = b '' Icc s t
    rw [hI, image_univ, himage]
  have hhalf : γ '' Ico (0 : unitInterval) 1 ⊆ b '' Ico s t := by
    rintro z ⟨u, hu, rfl⟩
    have hm : γ u ∈ b '' Icc s t := himage ▸ mem_range_self u
    obtain ⟨v, hv, hvu⟩ := hm
    have hvt : v ≠ t := by
      intro he
      have heq : u = 1 := hγi (hvu.symm.trans ((congrArg b he).trans h1.symm))
      exact hu.2.ne heq
    exact ⟨v, ⟨hv.1, lt_of_le_of_ne hv.2 hvt⟩, hvu⟩
  have hreverse : γ '' Ioc (0 : unitInterval) 1 ⊆ b '' Ioc s t := by
    rintro z ⟨u, hu, rfl⟩
    have hm : γ u ∈ b '' Icc s t := himage ▸ mem_range_self u
    obtain ⟨v, hv, hvu⟩ := hm
    have hvs : v ≠ s := by
      intro he
      have heq : u = 0 := hγi (hvu.symm.trans ((congrArg b he).trans h0.symm))
      exact hu.1.ne' heq
    exact ⟨v, ⟨lt_of_le_of_ne hv.1 (Ne.symm hvs), hv.2⟩, hvu⟩
  refine ⟨L, ?_⟩
  have hchain : PointRadialC1PlaneChain ha y (γ 0) (γ 1) L := hes.toPlane
  rw [h0, h1] at hchain
  refine ⟨hchain, ?_, hcarrier,
    hes.toPlane_halfOpen_pairwise hγi, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hne
    exact List.map_eq_nil_iff.mp he
  · intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact (hes.halfOpen_subset_total hγi hf).trans hhalf
  · intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact (hes.reverseHalfOpen_subset_total hγi hf).trans hreverse
  · intro e he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact f.toPlane_hasArgumentTurn hneq h0 hd
  · intro e he u hu
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact f.curve_no_interior_puncture hγi hu

/-- Source order proves the cross-chain half-open disjointness. -/
theorem PointBoundaryRadialChainOn.append
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {b : unitInterval → ℂ} (hbi : Function.Injective b)
    {s r t : unitInterval} (hsr : s < r) (hrt : r < t)
    {L M : List (PointRadialC1PlaneArc ha y)}
    (hL : PointBoundaryRadialChainOn ha y b s r L)
    (hM : PointBoundaryRadialChainOn ha y b r t M) :
    PointBoundaryRadialChainOn ha y b s t (L ++ M) := by
  have hinterval : Icc s r ∪ Icc r t = Icc s t := by
    ext u
    constructor
    · rintro (hu | hu)
      · exact ⟨hu.1, hu.2.trans hrt.le⟩
      · exact ⟨hsr.le.trans hu.1, hu.2⟩
    · intro hu
      by_cases hur : u ≤ r
      · exact Or.inl ⟨hu.1, hur⟩
      · exact Or.inr ⟨(lt_of_not_ge hur).le, hu.2⟩
  refine ⟨hL.chain.append hM.chain, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    exact hL.nonempty (List.append_eq_nil_iff.mp he).1
  · rw [pointRadialC1PlaneCarrier_append, hL.carrier, hM.carrier, ← image_union, hinterval]
  · rw [List.pairwise_append]
    refine ⟨hL.simple, hM.simple, ?_⟩
    intro e he f hf
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u, hu, huz⟩ := hL.halfOpen e he hz
    obtain ⟨v, hv, hvz⟩ := hM.halfOpen f hf hz'
    have heq := hbi (huz.trans hvz.symm)
    subst v
    exact not_le_of_gt hu.2 hv.1
  · intro e he z hz
    rcases List.mem_append.mp he with he | he
    · obtain ⟨u, hu, huz⟩ := hL.halfOpen e he hz
      exact ⟨u, ⟨hu.1, hu.2.trans hrt⟩, huz⟩
    · obtain ⟨u, hu, huz⟩ := hM.halfOpen e he hz
      exact ⟨u, ⟨hsr.le.trans hu.1, hu.2⟩, huz⟩
  · intro e he z hz
    rcases List.mem_append.mp he with he | he
    · obtain ⟨u, hu, huz⟩ := hL.reverseHalfOpen e he hz
      exact ⟨u, ⟨hu.1, hu.2.trans hrt.le⟩, huz⟩
    · obtain ⟨u, hu, huz⟩ := hM.reverseHalfOpen e he hz
      exact ⟨u, ⟨hsr.trans hu.1, hu.2⟩, huz⟩
  · intro e he
    exact (List.mem_append.mp he).elim (hL.argument e) (hM.argument e)
  · intro e he
    exact (List.mem_append.mp he).elim (hL.avoid e) (hM.avoid e)

/-- Finitely many actual transition times assemble the complete literal old
subarc; a local piece can itself contain many radial macro-arcs at ambient atoms. -/
theorem exists_boundary_radial_chain_of_finite_exceptions
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (b : unitInterval → ℂ) (hbi : Function.Injective b) (P : Finset unitInterval)
    (hlocal : ∀ s t : unitInterval, s < t →
      (∀ u ∈ Ioo s t, u ∉ P) →
      ∃ L, PointBoundaryRadialChainOn ha y b s t L)
    (s t : unitInterval) (hst : s < t) :
    ∃ L, PointBoundaryRadialChainOn ha y b s t L := by
  classical
  let K (s t : unitInterval) := P.filter (fun u => s < u ∧ u < t)
  have hmain : ∀ N : ℕ, ∀ s t : unitInterval, s < t → (K s t).card = N →
      ∃ L, PointBoundaryRadialChainOn ha y b s t L := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro s t hst hcard
      by_cases hne : (K s t).Nonempty
      · obtain ⟨r, hr⟩ := hne
        obtain ⟨hrP, hsr, hrt⟩ := Finset.mem_filter.mp hr
        have hleftsub : K s r ⊆ K s t := by
          intro u hu
          obtain ⟨huP, hsu, hur⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨huP, hsu, hur.trans hrt⟩
        have hrightsub : K r t ⊆ K s t := by
          intro u hu
          obtain ⟨huP, hru, hut⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨huP, hsr.trans hru, hut⟩
        have hrleft : r ∉ K s r := fun h => (lt_irrefl r) (Finset.mem_filter.mp h).2.2
        have hrright : r ∉ K r t := fun h => (lt_irrefl r) (Finset.mem_filter.mp h).2.1
        have hleftcard : (K s r).card < N := by
          rw [← hcard]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hleftsub, fun he => hrleft (he.symm ▸ hr)⟩)
        have hrightcard : (K r t).card < N := by
          rw [← hcard]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hrightsub, fun he => hrright (he.symm ▸ hr)⟩)
        obtain ⟨L, hL⟩ := ih (K s r).card hleftcard s r hsr rfl
        obtain ⟨M, hM⟩ := ih (K r t).card hrightcard r t hrt rfl
        exact ⟨L ++ M, hL.append hbi hsr hrt hM⟩
      · apply hlocal s t hst
        intro u hu huP
        exact hne ⟨u, Finset.mem_filter.mpr ⟨huP, hu⟩⟩
  exact hmain (K s t).card s t hst rfl

end RepulsiveCoulomb
