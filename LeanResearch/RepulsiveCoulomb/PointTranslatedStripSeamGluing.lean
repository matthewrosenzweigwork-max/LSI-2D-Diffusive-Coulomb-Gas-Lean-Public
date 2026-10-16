module

public import LeanResearch.RepulsiveCoulomb.MetricClosedCoverSeam
public import LeanResearch.RepulsiveCoulomb.TranslatedStripSeamSource
public import LeanResearch.RepulsiveCoulomb.PointMetricLineSideGeodesic

@[expose] public section

/-! SOURCE ONLY, UNCOMPILED. Actual all-pairs gluing of two successive literal
complex strips. The residual is the genuine set difference. The ambient
minimizer and its seam crossing are constructed from ambient geodesic convexity
and a closed two-set cover. No cross-distance, seam-chart, or desired extension
certificate is a premise. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- An actual ambient minimizer crosses a closed cover, and its distances add
at the crossing. Endpoints may already lie on the intersection. -/
theorem pointClosedCover_exists_additive_seam
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P S Q : Set ℂ}
    (hconv : PointGeodesicallyConvex a y P) (hS : IsClosed S) (hQ : IsClosed Q)
    (hcover : P = S ∪ Q) {x z : ℂ} (hxP : x∈P) (hzP : z∈P)
    (hx : x∈S) (hz : z∈Q) :
    ∃ p∈S∩Q,
      (pointSmoothConformalEDist a y x p).toReal +
        (pointSmoothConformalEDist a y p z).toReal =
          (pointSmoothConformalEDist a y x z).toReal := by
  obtain ⟨γ,h0,h1,hc,hγP,hd⟩ := hconv x hxP z hzP
  obtain ⟨t,ht⟩ := continuousPath_meets_closed_cover_intersection hS hQ γ hc
    (fun u ↦ hcover ▸ hγP u) (h0.symm ▸ hx) (h1.symm ▸ hz)
  refine ⟨γ t,ht,?_⟩
  have hleft := hd 0 t
  have hright := hd t 1
  rw [h0] at hleft
  rw [h1] at hright
  change (pointSmoothConformalEDist a y x (γ t)).toReal =
    |t.1-0| * (pointSmoothConformalEDist a y x z).toReal at hleft
  change (pointSmoothConformalEDist a y (γ t) z).toReal =
    |1-t.1| * (pointSmoothConformalEDist a y x z).toReal at hright
  rw [sub_zero,abs_of_nonneg t.2.1] at hleft
  rw [abs_of_nonneg (sub_nonneg.mpr t.2.2)] at hright
  rw [hleft,hright]
  ring

/-- Exact geometry carried by the newly constructed map. The source is the
literal Euclidean subtype, so there is no product-metric substitution. -/
structure PointTranslatedStripSeamGluing {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (P Q : Set ℂ) (v : ℂ)
    (b h : ℝ) (hb : 0≤b) (hh : 0≤h)
    (F : flatShearedStrip v b → P) (G : flatShearedStrip v h → Q) where
  map : flatShearedStrip v (b+h) → P
  metric : ∀ x z,(pointSmoothConformalEDist a y (map x).1 (map z).1).toReal=dist x z
  lower : ∀ x,map (translatedStripLowerInclusion hh x)=F x
  upper : ∀ z,(map (translatedStripUpperInclusion hb z)).1=(G z).1
  bottom : ∀ r,map (translatedStripBottom (add_nonneg hb hh) r)=F (translatedStripBottom hb r)
  top : ∀ r,(map (translatedStripTop (add_nonneg hb hh) r)).1=(G (translatedStripTop hh r)).1
  compact_edge_lower : ∀ u : Icc (0:ℝ) b,
    map (translatedStripEdge ⟨u.1,u.2.1,u.2.2.trans (le_add_of_nonneg_right hh)⟩)=
      F (translatedStripEdge u)
  compact_edge_upper : ∀ u : Icc (0:ℝ) h,
    (map (translatedStripEdge ⟨b+u.1,add_nonneg hb u.2.1,by linarith [u.2.2]⟩)).1=
      (G (translatedStripEdge u)).1
  image : range (fun x ↦ (map x).1)=range (fun x ↦ (F x).1) ∪ range (fun z ↦ (G z).1)
  closed : IsClosedEmbedding (fun x ↦ (map x).1)
  proper : IsProperMap (fun x ↦ (map x).1)

/-- The genuinely missing metric step: both inequalities for every cross-seam
pair. The lower inequality uses an actual ambient minimizer, not a minimizer
for a newly defined glued metric. The upper inequality uses the literal
straight source segment and includes its seam endpoint cases. -/
theorem pointTranslatedStrip_successive_cross_distance
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {v : ℂ} (hvi : v.im≠0) {b h : ℝ} (hb : 0≤b) (hh : 0≤h)
    (F : flatShearedStrip v b → P) (G : flatShearedStrip v h → Q)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hG : ∀ x z,(pointSmoothConformalEDist a y (G x).1 (G z).1).toReal=dist x z)
    (hconv : PointGeodesicallyConvex a y P) (hQclosed : IsClosed Q)
    (hQ : Q=P\(range (fun x ↦ (F x).1)\range (fun r ↦ (F (translatedStripTop hb r)).1)))
    (hseam : ∀ r,(G (translatedStripBottom hh r)).1=(F (translatedStripTop hb r)).1)
    (x : flatShearedStrip v b) (z : flatShearedStrip v h) :
    (pointSmoothConformalEDist a y (F x).1 (G z).1).toReal=
      dist (translatedStripLowerInclusion hh x) (translatedStripUpperInclusion hb z) := by
  let S := range (fun q ↦ (F q).1)
  let T := range (fun r ↦ (F (translatedStripTop hb r)).1)
  have hQP : Q⊆P := by rw [hQ]; exact diff_subset
  have hcover : P=S∪Q := by
    ext p
    constructor
    · intro hp
      by_cases hpS : p∈S
      · exact Or.inl hpS
      · right
        rw [hQ]
        exact ⟨hp,fun hn ↦ hpS hn.1⟩
    · rintro (⟨q,rfl⟩ | hp)
      · exact (F q).2
      · exact hQP hp
  have hmeet : S∩Q=T := by
    ext p
    constructor
    · rintro ⟨hpS,hpQ⟩
      rw [hQ] at hpQ
      by_contra hpT
      exact hpQ.2 ⟨hpS,hpT⟩
    · rintro ⟨r,rfl⟩
      refine ⟨mem_range_self _,?_⟩
      rw [hQ]
      exact ⟨(F (translatedStripTop hb r)).2,fun hn ↦ hn.2 (mem_range_self r)⟩
  have hSclosed : IsClosed S := (pointTranslatedStrip_closed_proper ha y hvi F hF).1.isClosed_range
  have hmetric_sum (r : NNReal) :
      dist x (translatedStripTop hb r)+dist (translatedStripBottom hh r) z=
      (pointSmoothConformalEDist a y (F x).1 (F (translatedStripTop hb r)).1).toReal+
        (pointSmoothConformalEDist a y (F (translatedStripTop hb r)).1 (G z).1).toReal := by
    rw [hF,← hseam r,hG]
  apply le_antisymm
  · obtain ⟨r,hr⟩ := translatedStrip_exists_source_seam_split hb hh x z
    calc
      (pointSmoothConformalEDist a y (F x).1 (G z).1).toReal ≤
          (pointSmoothConformalEDist a y (F x).1 (F (translatedStripTop hb r)).1).toReal+
          (pointSmoothConformalEDist a y (F (translatedStripTop hb r)).1 (G z).1).toReal :=
        @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
          (F x).1 (F (translatedStripTop hb r)).1 (G z).1
      _ = dist x (translatedStripTop hb r)+dist (translatedStripBottom hh r) z :=
        (hmetric_sum r).symm
      _ = _ := hr
  · obtain ⟨p,hp,hadd⟩ := pointClosedCover_exists_additive_seam hconv hSclosed hQclosed hcover
      (F x).2 (hQP (G z).2) (mem_range_self x) (G z).2
    rw [hmeet] at hp
    obtain ⟨r,hr⟩ := hp
    change (F (translatedStripTop hb r)).1 = p at hr
    calc
      dist (translatedStripLowerInclusion hh x) (translatedStripUpperInclusion hb z) ≤
          dist x.1 (translatedStripTop hb r).1+
            dist (translatedStripTop hb r).1 (translatedStripUpperInclusion hb z).1 :=
        dist_triangle x.1 (translatedStripTop hb r).1 (translatedStripUpperInclusion hb z).1
      _ = dist x (translatedStripTop hb r)+dist (translatedStripBottom hh r) z := by
        rw [translatedStrip_seam_distance hb hh r z]
        rfl
      _ = (pointSmoothConformalEDist a y (F x).1 p).toReal+
          (pointSmoothConformalEDist a y p (G z).1).toReal := by
        rw [hmetric_sum r,hr]
      _ = _ := hadd

/-- Construct the merged map and prove the ambient all-pairs isometry. Neither
its existence nor its cross-distance property is an input. -/
theorem pointTranslatedStrip_glue_successive
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {v : ℂ} (hvi : v.im≠0) {b h : ℝ} (hb : 0≤b) (hh : 0≤h)
    (F : flatShearedStrip v b → P) (G : flatShearedStrip v h → Q)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hG : ∀ x z,(pointSmoothConformalEDist a y (G x).1 (G z).1).toReal=dist x z)
    (hconv : PointGeodesicallyConvex a y P) (hQclosed : IsClosed Q)
    (hQ : Q=P\(range (fun x ↦ (F x).1)\range (fun r ↦ (F (translatedStripTop hb r)).1)))
    (hseam : ∀ r,(G (translatedStripBottom hh r)).1=(F (translatedStripTop hb r)).1) :
    Nonempty (PointTranslatedStripSeamGluing a y P Q v b h hb hh F G) := by
  classical
  have hQP : Q⊆P := by rw [hQ]; exact diff_subset
  let GP : flatShearedStrip v h → P := fun z ↦ ⟨(G z).1,hQP (G z).2⟩
  obtain ⟨H,hlo,hup⟩ := exists_map_of_jointly_surjective_injections
    (translatedStripLowerInclusion hh) (translatedStripUpperInclusion hb)
    (translatedStripLowerInclusion_injective hh) (translatedStripUpperInclusion_injective hb)
    (translatedStrip_successive_cover hb hh) F GP (by
      intro x z he
      obtain ⟨r,rfl,rfl⟩ := translatedStrip_successive_overlap hvi hb hh x z he
      exact Subtype.ext (hseam r).symm)
  have hupval (z) : (H (translatedStripUpperInclusion hb z)).1=(G z).1 :=
    congrArg Subtype.val (hup z)
  have hcross := pointTranslatedStrip_successive_cross_distance ha y hvi hb hh F G hF hG
    hconv hQclosed hQ hseam
  have hmetric : ∀ x z,(pointSmoothConformalEDist a y (H x).1 (H z).1).toReal=dist x z := by
    intro x z
    rcases translatedStrip_successive_cover hb hh x with ⟨u,rfl⟩ | ⟨u,rfl⟩
    · rcases translatedStrip_successive_cover hb hh z with ⟨w,rfl⟩ | ⟨w,rfl⟩
      · rw [hlo,hlo,hF]
        exact ((translatedStripLowerInclusion_isometry hh).dist_eq u w).symm
      · rw [hlo,hupval]
        exact hcross u w
    · rcases translatedStrip_successive_cover hb hh z with ⟨w,rfl⟩ | ⟨w,rfl⟩
      · rw [hupval,hlo,pointSmoothConformalEDist_comm,hcross,dist_comm]
      · rw [hupval,hupval,hG]
        exact ((translatedStripUpperInclusion_isometry hb).dist_eq u w).symm
  obtain ⟨hclosed,hproper⟩ := pointTranslatedStrip_closed_proper ha y hvi H hmetric
  refine ⟨{
    map := H
    metric := hmetric
    lower := hlo
    upper := hupval
    bottom := ?_
    top := ?_
    compact_edge_lower := ?_
    compact_edge_upper := ?_
    image := ?_
    closed := hclosed
    proper := hproper }⟩
  · intro r
    exact hlo (translatedStripBottom hb r)
  · intro r
    have he : translatedStripTop (v:=v) (add_nonneg hb hh) r=
        translatedStripUpperInclusion hb (translatedStripTop hh r) := by
      apply Subtype.ext
      simp only [translatedStripTop,translatedStripUpperInclusion_val,flatShearedPoint,Complex.ofReal_add]
      ring
    rw [he,hupval]
  · intro u
    exact hlo (translatedStripEdge u)
  · intro u
    have he : translatedStripEdge (v:=v)
        ⟨b+u.1,add_nonneg hb u.2.1,by linarith [u.2.2]⟩=
        translatedStripUpperInclusion hb (translatedStripEdge u) := by
      apply Subtype.ext
      simp only [translatedStripEdge,translatedStripUpperInclusion_val,flatShearedPoint,Complex.ofReal_add]
      ring
    rw [he,hupval]
  · ext p
    constructor
    · rintro ⟨q,rfl⟩
      rcases translatedStrip_successive_cover hb hh q with ⟨x,rfl⟩ | ⟨z,rfl⟩
      · exact Or.inl ⟨x,congrArg Subtype.val (hlo x).symm⟩
      · exact Or.inr ⟨z,(hupval z).symm⟩
    · rintro (⟨x,rfl⟩ | ⟨z,rfl⟩)
      · exact ⟨translatedStripLowerInclusion hh x,congrArg Subtype.val (hlo x)⟩
      · exact ⟨translatedStripUpperInclusion hb z,hupval z⟩

end RepulsiveCoulomb
