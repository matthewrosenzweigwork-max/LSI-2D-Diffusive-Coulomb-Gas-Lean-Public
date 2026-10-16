import LeanResearch.RepulsiveCoulomb.PointRadialC1PlaneArc

/-! Construct the literal cyclic list of C1 macro-arcs of an actual bigon,
retaining exact common-chart radial germs at every true vertex. The second
side is reversed in both list order and orientation. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

inductive PointRadialC1PlaneChain {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ℂ → ℂ → List (PointRadialC1PlaneArc ha y) → Prop
  | nil (p) : PointRadialC1PlaneChain ha y p p []
  | cons (e : PointRadialC1PlaneArc ha y) {q es} :
      PointRadialC1PlaneChain ha y e.finish q es → PointRadialC1PlaneChain ha y e.start q (e :: es)

namespace PointRadialC1PlaneChain

variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}

theorem append {p r q : ℂ} {es fs : List (PointRadialC1PlaneArc ha y)}
    (he : PointRadialC1PlaneChain ha y p r es) (hf : PointRadialC1PlaneChain ha y r q fs) :
    PointRadialC1PlaneChain ha y p q (es ++ fs) := by
  induction he with
  | nil => exact hf
  | cons e h ih => exact .cons e (ih hf)

theorem reverse {p q : ℂ} {es : List (PointRadialC1PlaneArc ha y)}
    (h : PointRadialC1PlaneChain ha y p q es) :
    PointRadialC1PlaneChain ha y q p ((es.map PointRadialC1PlaneArc.reverse).reverse) := by
  induction h with
  | nil => exact .nil _
  | cons e h ih =>
    have he : PointRadialC1PlaneChain ha y e.finish e.start [e.reverse] := by
      simpa only [PointRadialC1PlaneArc.reverse_start, PointRadialC1PlaneArc.reverse_finish] using
        (PointRadialC1PlaneChain.cons e.reverse (.nil e.reverse.finish))
    simpa only [List.map_cons, List.reverse_cons] using ih.append he

end PointRadialC1PlaneChain

variable {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}

theorem PointRadialC1ArcChain.toPlane {γ : Icc (0 : ℝ) 1 → ℂ}
    {s t : Icc (0 : ℝ) 1} {es : List (PointRadialC1ArcPiece ha y γ)}
    (h : PointRadialC1ArcChain ha y γ s t es) :
    PointRadialC1PlaneChain ha y (γ s) (γ t) (es.map PointRadialC1ArcPiece.toPlane) := by
  induction h with
  | nil => exact .nil _
  | cons e h ih =>
    have ht := ih
    rw [← e.at_one] at ht
    have he := PointRadialC1PlaneChain.cons e.toPlane ht
    change PointRadialC1PlaneChain ha y (e.curve 0) _ _ at he
    rw [e.at_zero] at he
    exact he

def pointRadialC1PlaneCarrier (es : List (PointRadialC1PlaneArc ha y)) : Set ℂ :=
  ⋃ e ∈ es, e.curve '' Icc (0 : ℝ) 1

theorem pointRadialC1PlaneCarrier_append (es fs : List (PointRadialC1PlaneArc ha y)) :
    pointRadialC1PlaneCarrier (es ++ fs) = pointRadialC1PlaneCarrier es ∪ pointRadialC1PlaneCarrier fs := by
  ext z
  simp only [pointRadialC1PlaneCarrier, mem_iUnion, mem_union]
  constructor
  · rintro ⟨e, he, hz⟩
    rcases List.mem_append.mp he with he | he
    · exact Or.inl ⟨e, he, hz⟩
    · exact Or.inr ⟨e, he, hz⟩
  · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
    · exact ⟨e, List.mem_append.mpr (Or.inl he), hz⟩
    · exact ⟨e, List.mem_append.mpr (Or.inr he), hz⟩

theorem pointRadialC1PlaneCarrier_reverse (es : List (PointRadialC1PlaneArc ha y)) :
    pointRadialC1PlaneCarrier ((es.map PointRadialC1PlaneArc.reverse).reverse) = pointRadialC1PlaneCarrier es := by
  apply Subset.antisymm
  · rintro z hz
    obtain ⟨e, hze⟩ := mem_iUnion.mp hz
    obtain ⟨he, hze⟩ := mem_iUnion.mp hze
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    rw [PointRadialC1PlaneArc.reverse_image] at hze
    exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hf, hze⟩⟩
  · intro z hz
    obtain ⟨e, hze⟩ := mem_iUnion.mp hz
    obtain ⟨he, hze⟩ := mem_iUnion.mp hze
    refine mem_iUnion.mpr ⟨e.reverse, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact List.mem_reverse.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
    · rwa [PointRadialC1PlaneArc.reverse_image]

theorem PointRadialC1ArcChain.toPlane_carrier {γ : Icc (0 : ℝ) 1 → ℂ}
    {s t : Icc (0 : ℝ) 1} {es : List (PointRadialC1ArcPiece ha y γ)}
    (h : PointRadialC1ArcChain ha y γ s t es) (hst : s < t) :
    pointRadialC1PlaneCarrier (es.map PointRadialC1ArcPiece.toPlane) = γ '' Icc s t := by
  rw [← h.exact_image hst]
  ext z
  simp only [pointRadialC1PlaneCarrier, mem_iUnion, List.mem_map]
  constructor
  · rintro ⟨e, ⟨f, hf, rfl⟩, hz⟩
    exact ⟨f, hf, hz⟩
  · rintro ⟨e, he, hz⟩
    exact ⟨e.toPlane, ⟨e, he, rfl⟩, hz⟩

/-- The actual two minimizing sides supply a positive finite cyclic smooth
list with exact coverage. No corner-angle or total-turn property is assumed. -/
theorem exists_pointConformal_radial_C1_bigon_cyclic_chain {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal) :
    ∃ es₁ : List (PointRadialC1ArcPiece ha y γ₁), ∃ es₂ : List (PointRadialC1ArcPiece ha y γ₂),
      PointRadialC1ArcChain ha y γ₁ ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ es₁ ∧
      PointRadialC1ArcChain ha y γ₂ ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ es₂ ∧
      let L := es₁.map PointRadialC1ArcPiece.toPlane ++
        ((es₂.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
      PointRadialC1PlaneChain ha y p p L ∧ 2 ≤ L.length ∧
        pointRadialC1PlaneCarrier L = range γ₁ ∪ range γ₂ := by
  obtain ⟨es₁, h₁, _, hne₁, him₁⟩ := exists_pointConformal_finite_radial_C1_arc_chain ha y hpq γ₁ hd₁
  obtain ⟨es₂, h₂, _, hne₂, him₂⟩ := exists_pointConformal_finite_radial_C1_arc_chain ha y hpq γ₂ hd₂
  have hp₁ := h₁.toPlane
  have hp₂ := h₂.toPlane
  rw [h10, h11] at hp₁
  rw [h20, h21] at hp₂
  have hI : Icc (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ = univ := by
    apply eq_univ_of_forall
    intro u
    exact u.2
  have hm₁ := h₁.toPlane_carrier (by norm_num)
  have hm₂ := h₂.toPlane_carrier (by norm_num)
  rw [hI, image_univ] at hm₁ hm₂
  refine ⟨es₁, es₂, h₁, h₂, hp₁.append hp₂.reverse, ?_, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_reverse]
    have hlen₁ := List.length_pos_iff.mpr hne₁
    have hlen₂ := List.length_pos_iff.mpr hne₂
    omega
  · rw [pointRadialC1PlaneCarrier_append, pointRadialC1PlaneCarrier_reverse, hm₁, hm₂]

end RepulsiveCoulomb
