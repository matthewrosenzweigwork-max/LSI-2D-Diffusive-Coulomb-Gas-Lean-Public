module

public import LeanResearch.RepulsiveCoulomb.PointActualRetainedApexSectorRemoval

@[expose] public section

/-!
NEW SUCCESSOR, SOURCE-ONLY, NOT COMPILED. The original frozen body is unchanged.
Local classical decidability supplies membership in the arbitrary real parameter
set. Preserve an actual finite geodesic boundary cover.
Each old piece is restricted to the new geodesically convex closed region; its
parameter set is proved closed and order-convex by actual geodesic uniqueness.
No certificate that the bent entire boundary is geodesic is used.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem PointClosedBoundaryGeodesicPiece.exists_closed_convex_restriction_classical
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (E : PointClosedBoundaryGeodesicPiece a y) {Q : Set ℂ}
    (hQ : IsClosed Q) (hconv : PointGeodesicallyConvex a y Q) :
    ∃ F : PointClosedBoundaryGeodesicPiece a y, range F.curve = range E.curve ∩ Q := by
  classical
  let r : ℝ → ℂ := fun t ↦ if ht : t ∈ E.interval then E.curve ⟨t,ht⟩ else 0
  have hr (t : ℝ) (ht : t ∈ E.interval) : r t = E.curve ⟨t,ht⟩ := dif_pos ht
  let J : Set ℝ := E.interval ∩ r ⁻¹' Q
  have hJeq : J = Subtype.val '' (E.curve ⁻¹' Q) := by
    ext t
    constructor
    · rintro ⟨htI,htQ⟩
      exact ⟨⟨t,htI⟩,by simpa only [Set.mem_preimage, hr t htI] using htQ,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t.2,by simpa only [Set.mem_preimage, hr t t.2] using ht⟩
  have hJclosed : IsClosed J := by
    rw [hJeq]
    exact E.interval_closed.isClosedEmbedding_subtypeVal.isClosedMap _
      (hQ.preimage (E.closedEmbedding ha y).continuous)
  have hJord : OrdConnected J := by
    refine ⟨?_⟩
    intro s hs t ht u hu
    have huI : u ∈ E.interval := E.interval_convex.ordConnected.out hs.1 ht.1 hu
    refine ⟨huI,?_⟩
    rcases eq_or_lt_of_le (hu.1.trans hu.2) with heq | hst
    · have he : u = s := le_antisymm (hu.2.trans heq.ge) hu.1
      exact he.symm ▸ hs.2
    · have hinside (v : ℝ) (hv : v ∈ Icc s t) : v ∈ E.interval :=
        E.interval_convex.ordConnected.out hs.1 ht.1 hv
      have hd : ∀ v ∈ Icc s t, ∀ w ∈ Icc s t,
          (pointSmoothConformalEDist a y (r v) (r w)).toReal = dist v w := by
        intro v hv w hw
        rw [hr v (hinside v hv),hr w (hinside w hw)]
        exact E.metric _ _
      let γ := lineCapSegment r s t
      have hγ := lineCapSegment_metricOn y r hst.le hd
      obtain ⟨η,hη0,hη1,_,hηQ,hηd⟩ := hconv (r s) hs.2 (r t) ht.2
      have heq : γ = η := pointConformal_geodesic_unique ha y (r s) (r t) γ η
        (lineCapSegment_zero r s t) (lineCapSegment_one r s t) hη0 hη1 hγ hηd
      have hm : r u ∈ range γ := by
        rw [lineCapSegment_range r hst]
        exact ⟨u,hu,rfl⟩
      obtain ⟨v,hv⟩ := hm
      change r u ∈ Q
      rw [← hv,heq]
      exact hηQ v
  let F : PointClosedBoundaryGeodesicPiece a y :=
    { interval := J
      interval_closed := hJclosed
      interval_convex := hJord.convex
      curve := fun t ↦ E.curve ⟨t.1,t.2.1⟩
      metric := fun s t ↦ E.metric _ _ }
  refine ⟨F,?_⟩
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨mem_range_self _, ?_⟩
    change E.curve ⟨t.1, t.2.1⟩ ∈ Q
    simpa only [Set.mem_preimage, hr t.1 t.2.1] using t.2.2
  · rintro ⟨⟨t,rfl⟩,htQ⟩
    exact ⟨⟨t.1,t.2,by simpa only [Set.mem_preimage, hr t.1 t.2] using htQ⟩,rfl⟩

/-- A literal new ray plus the retained old boundary have a finite actual
geodesic-piece cover. Empty restricted old pieces cause no difficulty. -/
theorem pointRetainedSector_construct_finite_boundary_cover_classical
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} (hP : IsClosed P) (hQ : IsClosed Q) (hQP : Q ⊆ P)
    (hconv : PointGeodesicallyConvex a y Q)
    (old : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hold : frontier P = ⋃ i, range (old i).curve)
    (top : NNReal → ℂ)
    (htop : ∀ s t, (pointSmoothConformalEDist a y (top s) (top t)).toReal = dist s t)
    (hTfront : range top ⊆ frontier Q)
    (hfront : frontier Q ⊆ range top ∪ frontier P) :
    ∃ fresh : Fin (N+1) → PointClosedBoundaryGeodesicPiece a y,
      frontier Q = ⋃ i, range (fresh i).curve := by
  classical
  choose pieces hpieces using
    (fun i : Fin N ↦ (old i).exists_closed_convex_restriction_classical ha y hQ hconv)
  let T : PointClosedBoundaryGeodesicPiece a y :=
    { interval := Ici (0:ℝ)
      interval_closed := isClosed_Ici
      interval_convex := convex_Ici 0
      curve := fun t ↦ top ⟨t.1,t.2⟩
      metric := fun s t ↦ htop _ _ }
  have hT : range T.curve = range top := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩; exact mem_range_self _
    · rintro ⟨t,rfl⟩; exact ⟨⟨t.1,t.2⟩,rfl⟩
  let fresh : Fin (N+1) → PointClosedBoundaryGeodesicPiece a y := Fin.cases T pieces
  refine ⟨fresh,?_⟩
  ext z
  constructor
  · intro hz
    rcases hfront hz with hzT | hzP
    · apply mem_iUnion.mpr
      exact ⟨0,by change z ∈ range T.curve; rwa [hT]⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp (hold ▸ hzP)
      apply mem_iUnion.mpr
      refine ⟨i.succ,?_⟩
      change z ∈ range (pieces i).curve
      rw [hpieces i]
      exact ⟨hi,hQ.frontier_subset hz⟩
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    refine Fin.cases ?_ (fun j ↦ ?_) i hi
    · intro hzT
      apply hTfront
      change z ∈ range T.curve at hzT
      rwa [hT] at hzT
    · intro hzOld
      change z ∈ range (pieces j).curve at hzOld
      rw [hpieces j] at hzOld
      have hzP : z ∈ frontier P := hold.symm ▸ mem_iUnion.mpr ⟨j,hzOld.1⟩
      refine ⟨subset_closure hzOld.2,?_⟩
      intro hzI
      exact hzP.2 (interior_mono hQP hzI)

end RepulsiveCoulomb
