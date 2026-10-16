module

public import LeanResearch.RepulsiveCoulomb.ShearedRectangleInteriorGeometry
public import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfplaneHomeomorphisms
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Uses the accepted literal complex strip
`flatShearedStrip`, not a product metric. `flatShearHomeomorph` is itself a NEW
source-only dependency from the normal-source-geometry draft; no acceptance is
claimed for that dependency or for this file. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def translatedStripBottom {v : ℂ} {b : ℝ} (hb : 0 ≤ b) (r : NNReal) :
    flatShearedStrip v b :=
  ⟨flatShearedPoint v r 0, r, r.2, 0, ⟨le_rfl, hb⟩, rfl⟩

def translatedStripTop {v : ℂ} {b : ℝ} (hb : 0 ≤ b) (r : NNReal) :
    flatShearedStrip v b :=
  ⟨flatShearedPoint v r b, r, r.2, b, ⟨hb, le_rfl⟩, rfl⟩

def translatedStripEdge {v : ℂ} {b : ℝ} (u : Icc (0 : ℝ) b) :
    flatShearedStrip v b :=
  ⟨flatShearedPoint v 0 u, 0, le_rfl, u, u.2, rfl⟩

theorem flatShearedPoint_coordinates_eq {v : ℂ} (hvi : v.im ≠ 0)
    {r u s w : ℝ} (h : flatShearedPoint v r u = flatShearedPoint v s w) :
    r = s ∧ u = w := by
  have he : (r, u) = (s, w) := (flatShearHomeomorph hvi).injective h
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem translatedStripBottom_isometry {v : ℂ} {b : ℝ} (hb : 0 ≤ b) :
    Isometry (@translatedStripBottom v b hb) := by
  apply Isometry.of_dist_eq
  intro r s
  change dist (flatShearedPoint v r 0) (flatShearedPoint v s 0) = dist r s
  simp only [flatShearedPoint_zero, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, NNReal.dist_eq]

theorem translatedStripTop_isometry {v : ℂ} {b : ℝ} (hb : 0 ≤ b) :
    Isometry (@translatedStripTop v b hb) := by
  apply Isometry.of_dist_eq
  intro r s
  change dist (flatShearedPoint v r b) (flatShearedPoint v s b) = dist r s
  change dist (((r : ℝ) : ℂ) + (b : ℂ) * v)
    (((s : ℝ) : ℂ) + (b : ℂ) * v) = dist r s
  rw [dist_add_right]
  simp only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, NNReal.dist_eq]

theorem flatShearedStrip_image {v : ℂ} {b : ℝ} (hvi : v.im ≠ 0) :
    flatShearedStrip v b = (flatShearHomeomorph hvi) ''
      (Ici (0 : ℝ) ×ˢ Icc (0 : ℝ) b) := by
  ext z
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    exact ⟨(r, u), ⟨hr, hu⟩, rfl⟩
  · rintro ⟨⟨r,u⟩, ⟨hr,hu⟩, rfl⟩
    exact ⟨r, hr, u, hu, rfl⟩

theorem flatShearedStrip_isClosed {v : ℂ} {b : ℝ} (hvi : v.im ≠ 0) :
    IsClosed (flatShearedStrip v b) := by
  rw [flatShearedStrip_image hvi]
  exact (flatShearHomeomorph hvi).isClosedMap _ (isClosed_Ici.prod isClosed_Icc)

theorem flatShearedStrip_isometry_closed_proper {Y : Type*} [MetricSpace Y]
    {v : ℂ} {b : ℝ} (hvi : v.im ≠ 0) {F : flatShearedStrip v b → Y}
    (hF : Isometry F) : IsClosedEmbedding F ∧ IsProperMap F := by
  letI : CompleteSpace (flatShearedStrip v b) :=
    (flatShearedStrip_isClosed hvi).isComplete.completeSpace_coe
  exact ⟨hF.isClosedEmbedding, hF.isClosedEmbedding.isProperMap⟩

theorem translatedStrip_image_mem_top_iff {Y : Type*} {v : ℂ} {b : ℝ}
    (hvi : v.im ≠ 0) (hb : 0 ≤ b) {F : flatShearedStrip v b → Y}
    (hF : Function.Injective F) (x : flatShearedStrip v b)
    {r u : ℝ} (hr : 0 ≤ r) (hxu : x.1 = flatShearedPoint v r u) :
    F x ∈ range (F ∘ translatedStripTop hb) ↔ u = b := by
  constructor
  · rintro ⟨s, hs⟩
    have he := congrArg Subtype.val (hF hs)
    change flatShearedPoint v s b = x.1 at he
    rw [hxu] at he
    exact (flatShearedPoint_coordinates_eq hvi he).2.symm
  · intro hu
    refine ⟨⟨r, hr⟩, congrArg F (Subtype.ext ?_)⟩
    change flatShearedPoint v r b = x.1
    rw [hxu, hu]

theorem translatedStrip_without_top_connected {Y : Type*} [TopologicalSpace Y]
    {v : ℂ} {b : ℝ} (hvi : v.im ≠ 0) (hb : 0 < b)
    (F : flatShearedStrip v b → Y) (hF : Continuous F) (hinj : Function.Injective F) :
    IsConnected (range F \ range (F ∘ translatedStripTop hb.le)) := by
  let K : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ Ico (0 : ℝ) b
  have hKconvex : Convex ℝ K := (convex_Ici 0).prod (convex_Ico 0 b)
  have hK : IsConnected K := ⟨⟨(0,0), by simp [K,hb]⟩,hKconvex.isPreconnected⟩
  letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hK
  let i : K → flatShearedStrip v b := fun q ↦
    ⟨flatShearedPoint v q.1.1 q.1.2, q.1.1, q.2.1, q.1.2,
      ⟨q.2.2.1,q.2.2.2.le⟩,rfl⟩
  have hi : Continuous i := by
    apply Continuous.subtype_mk
    exact (flatShearHomeomorph hvi).continuous.comp continuous_subtype_val
  have him : range (F ∘ i) = range F \ range (F ∘ translatedStripTop hb.le) := by
    ext z
    constructor
    · rintro ⟨q,rfl⟩
      refine ⟨mem_range_self (i q),?_⟩
      change F (i q) ∉ range (F ∘ translatedStripTop hb.le)
      rw [translatedStrip_image_mem_top_iff hvi hb.le hinj (i q) q.2.1 rfl]
      exact ne_of_lt q.2.2.2
    · rintro ⟨⟨x,rfl⟩,hxt⟩
      obtain ⟨r,hr,u,hu,hxu⟩ := x.2
      have hub : u < b := lt_of_le_of_ne hu.2 (fun he ↦
        hxt ((translatedStrip_image_mem_top_iff hvi hb.le hinj x hr hxu).mpr he))
      refine ⟨⟨(r,u),hr,hu.1,hub⟩,?_⟩
      exact congrArg F (Subtype.ext hxu.symm)
  rw [← him]
  exact isConnected_range (hF.comp hi)

/-- The strip source is closed and complete, so these facts are conclusions
of its supplied actual isometry, not hypotheses about the residual. -/
theorem pointTranslatedStrip_closed_proper
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {v : ℂ} {b : ℝ} (hvi : v.im ≠ 0)
    (F : flatShearedStrip v b → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) :
    IsClosedEmbedding (fun x ↦ (F x).1) ∧ IsProperMap (fun x ↦ (F x).1) := by
  have hi : @Isometry (flatShearedStrip v b) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace (fun x ↦ (F x).1) :=
    @Isometry.of_dist_eq _ ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace _ hF
  have hc := @flatShearedStrip_isometry_closed_proper ℂ
    (pointSmoothConformalMetricSpace ha y) v b hvi _ hi
  have hclosed : @IsClosedEmbedding (flatShearedStrip v b) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (fun x ↦ (F x).1) := hc.1
  have hproper : @IsProperMap (flatShearedStrip v b) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace
      (fun x ↦ (F x).1) := hc.2
  rw [pointSmoothConformalMetricSpace_topology ha y] at hclosed hproper
  exact ⟨hclosed,hproper⟩

/-- Exact old-boundary contact puts every positive-time top point in the OLD
interior. Top marks are allowed. The endpoint z is deliberately excluded. -/
theorem pointTranslatedStrip_open_top_interior
    {P : Set ℂ} {v : ℂ} {b : ℝ} (hvi : v.im ≠ 0) (hb : 0 < b)
    (F : flatShearedStrip v b → P) (hinj : Function.Injective (fun x ↦ (F x).1))
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1)) :
    ∀ r : NNReal, 0 < r → (F (translatedStripTop hb.le r)).1 ∈ interior P := by
  intro r hr
  by_contra hnot
  have hf : (F (translatedStripTop hb.le r)).1 ∈ frontier P :=
    ⟨subset_closure (F (translatedStripTop hb.le r)).2,hnot⟩
  have hc : (F (translatedStripTop hb.le r)).1 ∈
      range (fun s ↦ (F (translatedStripBottom hb.le s)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1) := by
    rw [← hcontact]
    exact ⟨⟨translatedStripTop hb.le r, rfl⟩, hf⟩
  rcases hc with ⟨s,hs⟩ | ⟨u,hu⟩
  · have he := congrArg Subtype.val (hinj hs)
    change flatShearedPoint v s 0 = flatShearedPoint v r b at he
    exact hb.ne (flatShearedPoint_coordinates_eq hvi he).2
  · have he := congrArg Subtype.val (hinj hu)
    change flatShearedPoint v 0 u = flatShearedPoint v r b at he
    have hr0 : (r : ℝ) = 0 := (flatShearedPoint_coordinates_eq hvi he).1.symm
    exact (ne_of_gt hr) (Subtype.ext hr0)


/-- An actual forward old-boundary ray is constructed directly from the OLD
ambient straightening. Its orientation is the positive real-coordinate end. -/
def translatedOldForwardRay (H : ℂ ≃ₜ ℂ) (z : ℂ) (r : NNReal) : ℂ :=
  H.symm (H z + ((r : ℝ) : ℂ))

@[simp] theorem translatedOldForwardRay_zero (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    translatedOldForwardRay H z 0 = z := by simp [translatedOldForwardRay]

theorem translatedOldForwardRay_isClosedEmbedding (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    IsClosedEmbedding (translatedOldForwardRay H z) := by
  have hi : Isometry (fun r : NNReal ↦ H z + ((r : ℝ) : ℂ)) := by
    apply Isometry.of_dist_eq
    intro r s
    rw [dist_add_left,dist_eq_norm,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,NNReal.dist_eq]
  exact H.symm.isClosedEmbedding.comp hi.isClosedEmbedding

/-- Every bottom point, including p, is genuinely below the top. -/
theorem translatedStrip_bottom_not_top {Y : Type*} {v : ℂ} {b : ℝ}
    (hvi : v.im ≠ 0) (hb : 0 < b) {F : flatShearedStrip v b → Y}
    (hinj : Function.Injective F) (r : NNReal) :
    F (translatedStripBottom hb.le r) ∉ range (F ∘ translatedStripTop hb.le) := by
  rw [translatedStrip_image_mem_top_iff hvi hb.le hinj
    (translatedStripBottom hb.le r) r.2 rfl]
  exact hb.ne

/-- Every point of the compact edge except z is genuinely below the top. -/
theorem translatedStrip_edge_not_top {Y : Type*} {v : ℂ} {b : ℝ}
    (hvi : v.im ≠ 0) (hb : 0 < b) {F : flatShearedStrip v b → Y}
    (hinj : Function.Injective F) (u : Icc (0 : ℝ) b) (hu : u.1 < b) :
    F (translatedStripEdge u) ∉ range (F ∘ translatedStripTop hb.le) := by
  rw [translatedStrip_image_mem_top_iff hvi hb.le hinj
    (translatedStripEdge u) (le_refl (0 : ℝ)) rfl]
  exact ne_of_lt hu

/-- The transported atom moves between two distinct actual ambient points. -/
theorem translatedStrip_apex_ne_top_origin {Y : Type*} {v : ℂ} {b : ℝ}
    (hvi : v.im ≠ 0) (hb : 0 < b) {F : flatShearedStrip v b → Y}
    (hinj : Function.Injective F) :
    F (translatedStripBottom hb.le 0) ≠ F (translatedStripTop hb.le 0) := by
  intro he
  exact translatedStrip_bottom_not_top hvi hb hinj 0 ⟨0,he.symm⟩

end RepulsiveCoulomb
