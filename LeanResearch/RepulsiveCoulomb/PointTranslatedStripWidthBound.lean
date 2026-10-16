module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripUnboundedUnion
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRelativeFullness

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. Infinite-width exhaustion is proved from genuine stage
maps, their exact old-boundary contact, actual admissible old charts and clean
interior points. Relative openness is DERIVED by finite-strip local fullness.
There is no exhaustion, image-openness or boundary-angle-matching premise.

These are continuation helpers. The enclosing construction must construct the
compatible stage family and find an excluded budget point from its ORIGINAL
geometry; the theorems do not pretend to construct that family or budget point.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

private theorem translatedStrip_value_without_top_eq
    {P : Set ℂ} {v : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (f : flatShearedStrip v s → P) :
    {p : P | p.1 ∈ range (fun z ↦ (f z).1) \
      range (fun r ↦ (f (translatedStripTop hs r)).1)} =
      range f \ range (f ∘ translatedStripTop hs) := by
  ext p
  constructor
  · rintro ⟨⟨z, hz⟩, htop⟩
    refine ⟨⟨z, Subtype.ext hz⟩, ?_⟩
    rintro ⟨r, hr⟩
    exact htop ⟨r, congrArg Subtype.val hr⟩
  · rintro ⟨⟨z, hz⟩, htop⟩
    refine ⟨⟨z, congrArg Subtype.val hz⟩, ?_⟩
    rintro ⟨r, hr⟩
    exact htop ⟨r, Subtype.ext hr⟩

/-- An unbounded compatible family of actual regular translated strips covers
its connected target. The closed-wedge image is the union of the relatively
open below-top stage images, so it is both closed and open. The two old-end
local fullness statements are supplied by proved geometric finite-strip
fullness, not by assumed topological or angle certificates. -/
theorem pointTranslatedStrip_unbounded_widths_exhaust
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hconn : IsPreconnected P)
    {stripAngle : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    {W : Set ℝ} (hW : ¬ BddAbove W) (hWpos : ∀ s ∈ W, 0 < s)
    (f : ∀ s : W, flatShearedStrip (conePhase stripAngle) s.1 → P)
    (hd : ∀ s x z,
      (pointSmoothConformalEDist a y (f s x).1 (f s z).1).toReal = dist x z)
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedStrip (conePhase stripAngle) s.1)
      (ht : z ∈ flatShearedStrip (conePhase stripAngle) t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩)
    (hcontact : ∀ s : W, range (fun z ↦ (f s z).1) ∩ frontier P =
      range (fun r ↦ (f s (translatedStripBottom (hWpos s.1 s.2).le r)).1) ∪
      range (fun u ↦ (f s (translatedStripEdge u)).1))
    (hcharts : ∀ p ∈ frontier P,
      ∃ C : PointRetainedConeNeighborhood a y P p, C.Admissible)
    (hcleanInterior : ∀ s : W, ∀ p ∈ interior P,
      p ∈ range (fun z ↦ (f s z).1) \
        range (fun r ↦ (f s (translatedStripTop (hWpos s.1 s.2).le r)).1) →
      coalescedPointExponent a y p = 0) :
    ∀ p : P, ∃ s : W, ∃ z : flatShearedStrip (conePhase stripAngle) s.1, f s z = p := by
  let U : W → Set ℂ := fun s ↦ flatShearedStrip (conePhase stripAngle) s.1
  let G : (⋃ s, U s) → P := directedFlatUnion U f hcompat
  have hvi : (conePhase stripAngle).im ≠ 0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  have hf : ∀ s, @Isometry (U s) P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace (f s) := by
    intro s
    exact @Isometry.of_dist_eq _ P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace
      (f s) (hd s)
  have hGc : IsClosed (range G) := by
    have hc : @IsClosed P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
        (range G) :=
      @shearedStripUnion_isClosed_range P (pointRegionMetricSpace ha y P)
        (conePhase stripAngle) hvi W hW f hf hcompat
    rwa [pointRegionMetricSpace_topology ha y P] at hc
  have hGo : IsOpen (range G) := by
    have he := @shearedStripUnion_range_eq_iUnion_without_top P
      (pointRegionMetricSpace ha y P) (conePhase stripAngle) hvi W hW hWpos f hf hcompat
    change range G = _ at he
    rw [he]
    apply isOpen_iUnion
    intro s
    have ho := pointTranslatedStrip_without_top_relatively_open ha y stripAngle_pos stripAngle_lt_pi
      (hWpos s.1 s.2) (f s) (hd s) (hcontact s) hcharts (hcleanInterior s)
    rwa [translatedStrip_value_without_top_eq] at ho
  have hGne : (range G).Nonempty := by
    obtain ⟨s, hs, h0s⟩ := not_bddAbove_iff.mp hW 0
    let j : W := ⟨s, hs⟩
    let x := translatedStripBottom (v := conePhase stripAngle) (hWpos j.1 j.2).le 0
    exact ⟨G ⟨x.1, mem_iUnion.mpr ⟨j, x.2⟩⟩, mem_range_self _⟩
  letI : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hconn
  have hGall : range G = univ := (show IsClopen (range G) from ⟨hGc, hGo⟩).eq_univ hGne
  intro p
  have hp : p ∈ range G := by rw [hGall]; trivial
  obtain ⟨x, hx⟩ := hp
  obtain ⟨s, hs⟩ := mem_iUnion.mp x.2
  exact ⟨s, ⟨x.1, hs⟩, (directedFlatUnion_of_mem U f hcompat x s hs).symm.trans hx⟩

/-- One genuinely excluded target point forbids infinite width. In the signed
budget construction this point is obtained from positive total budget and zero
budget at the original corner; it is not an assumed finiteness certificate. -/
theorem pointTranslatedRegularWidths_bddAbove
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hconn : IsPreconnected P)
    {stripAngle : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    {W : Set ℝ} (hWpos : ∀ s ∈ W, 0 < s)
    (f : ∀ s : W, flatShearedStrip (conePhase stripAngle) s.1 → P)
    (hd : ∀ s x z,
      (pointSmoothConformalEDist a y (f s x).1 (f s z).1).toReal = dist x z)
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedStrip (conePhase stripAngle) s.1)
      (ht : z ∈ flatShearedStrip (conePhase stripAngle) t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩)
    (hcontact : ∀ s : W, range (fun z ↦ (f s z).1) ∩ frontier P =
      range (fun r ↦ (f s (translatedStripBottom (hWpos s.1 s.2).le r)).1) ∪
      range (fun u ↦ (f s (translatedStripEdge u)).1))
    (hcharts : ∀ p ∈ frontier P,
      ∃ C : PointRetainedConeNeighborhood a y P p, C.Admissible)
    (hcleanInterior : ∀ s : W, ∀ p ∈ interior P,
      p ∈ range (fun z ↦ (f s z).1) \
        range (fun r ↦ (f s (translatedStripTop (hWpos s.1 s.2).le r)).1) →
      coalescedPointExponent a y p = 0)
    (q : P) (hq : ∀ s : W, q.1 ∉ range (fun z ↦ (f s z).1)) :
    BddAbove W := by
  by_contra hW
  obtain ⟨s, z, hz⟩ := pointTranslatedStrip_unbounded_widths_exhaust ha y hconn stripAngle_pos stripAngle_lt_pi
    hW hWpos f hd hcompat hcontact hcharts hcleanInterior q
  exact hq s ⟨z, congrArg Subtype.val hz⟩

end RepulsiveCoulomb
