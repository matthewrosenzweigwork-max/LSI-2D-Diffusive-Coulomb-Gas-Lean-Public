module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripSeamGluing

@[expose] public section

/-! SOURCE ONLY, UNCOMPILED. Boundary consequences of actual seam gluing.
The new compact edge is proved to lie on the original frontier from the genuine
residual frontier and injectivity. No old-boundary contact of the merged map
is assumed. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- A new compact edge on the residual frontier cannot run along the common
top except at its origin: the new strip's isometry excludes that overlap. -/
theorem pointTranslatedStrip_new_edge_old_frontier
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {v : ℂ} (hvi : v.im≠0) {b h : ℝ} (hb : 0≤b) (hh : 0≤h)
    (F : flatShearedStrip v b → P) (G : flatShearedStrip v h → Q)
    (hG : ∀ x z,(pointSmoothConformalEDist a y (G x).1 (G z).1).toReal=dist x z)
    (hseam : ∀ r,(G (translatedStripBottom hh r)).1=(F (translatedStripTop hb r)).1)
    (hFedge : ∀ u,(F (translatedStripEdge u)).1∈frontier P)
    (hGedge : ∀ u,(G (translatedStripEdge u)).1∈frontier Q)
    (hfront : frontier Q ⊆ range (fun r ↦ (F (translatedStripTop hb r)).1) ∪ frontier P) :
    ∀ u : Icc (0:ℝ) h,(G (translatedStripEdge u)).1∈frontier P := by
  have hinj := (pointTranslatedStrip_closed_proper ha y hvi G hG).1.injective
  intro u
  rcases hfront (hGedge u) with ⟨r,hr⟩ | hp
  · have he := congrArg Subtype.val (hinj ((hseam r).trans hr))
    change flatShearedPoint v r 0=flatShearedPoint v 0 u.1 at he
    have hr0 : r=0 := Subtype.ext (flatShearedPoint_coordinates_eq hvi he).1
    rw [← hr,hr0]
    exact hFedge ⟨b,hb,le_rfl⟩
  · exact hp

namespace PointTranslatedStripSeamGluing

/-- The merged source has exactly its original bottom and the concatenated
compact edge on the original boundary. Positivity of r and u in the new piece
is checked using its produced interior property, including the new open top. -/
theorem exact_old_boundary_contact
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {v : ℂ} (hvi : v.im≠0) {b h : ℝ} (hb : 0≤b) (hh : 0≤h)
    (F : flatShearedStrip v b → P) (G : flatShearedStrip v h → Q)
    (E : PointTranslatedStripSeamGluing a y P Q v b h hb hh F G)
    (hG : ∀ x z,(pointSmoothConformalEDist a y (G x).1 (G z).1).toReal=dist x z)
    (hseam : ∀ r,(G (translatedStripBottom hh r)).1=(F (translatedStripTop hb r)).1)
    (hQP : Q⊆P)
    (hFcontact : range (fun x ↦ (F x).1)∩frontier P=
      range (fun r ↦ (F (translatedStripBottom hb r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (hGedge : ∀ u,(G (translatedStripEdge u)).1∈frontier Q)
    (hfront : frontier Q ⊆ range (fun r ↦ (F (translatedStripTop hb r)).1) ∪ frontier P)
    (hGinterior : ∀ r : NNReal,0<r → ∀ u : Icc (0:ℝ) h,0<u.1 →
      (G ⟨flatShearedPoint v r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1∈interior Q) :
    range (fun x ↦ (E.map x).1)∩frontier P=
      range (fun r ↦ (E.map (translatedStripBottom (add_nonneg hb hh) r)).1) ∪
      range (fun u ↦ (E.map (translatedStripEdge u)).1) := by
  have hFbottom (r) : (F (translatedStripBottom hb r)).1∈frontier P := by
    have hc : (F (translatedStripBottom hb r)).1∈range (fun x ↦ (F x).1)∩frontier P := by
      rw [hFcontact]
      exact Or.inl (mem_range_self r)
    exact hc.2
  have hFedge (u) : (F (translatedStripEdge u)).1∈frontier P := by
    have hc : (F (translatedStripEdge u)).1∈range (fun x ↦ (F x).1)∩frontier P := by
      rw [hFcontact]
      exact Or.inr (mem_range_self u)
    exact hc.2
  have hGedgeP := pointTranslatedStrip_new_edge_old_frontier ha y hvi hb hh F G hG hseam
    hFedge hGedge hfront
  have hOld (x) (hx : (F x).1∈frontier P) :
      (F x).1∈range (fun r ↦ (E.map (translatedStripBottom (add_nonneg hb hh) r)).1) ∪
        range (fun u ↦ (E.map (translatedStripEdge u)).1) := by
    have hc : (F x).1∈range (fun q ↦ (F q).1)∩frontier P := ⟨mem_range_self x,hx⟩
    rw [hFcontact] at hc
    rcases hc with ⟨r,hr⟩ | ⟨u,hu⟩
    · left
      exact ⟨r,(congrArg Subtype.val (E.bottom r)).trans hr⟩
    · right
      exact ⟨⟨u.1,u.2.1,u.2.2.trans (le_add_of_nonneg_right hh)⟩,
        (congrArg Subtype.val (E.compact_edge_lower u)).trans hu⟩
  ext p
  constructor
  · rintro ⟨⟨q,rfl⟩,hqfront⟩
    dsimp only at hqfront ⊢
    rcases translatedStrip_successive_cover hb hh q with ⟨x,rfl⟩ | ⟨z,rfl⟩
    · rw [E.lower] at hqfront ⊢
      exact hOld x hqfront
    · rw [E.upper] at hqfront ⊢
      obtain ⟨r,hr,u,hu,hz⟩ := z.2
      by_cases hr0 : r=0
      · right
        have he : z=translatedStripEdge (v:=v) ⟨u,hu⟩ :=
          Subtype.ext (by
            change z.1 = flatShearedPoint v 0 u
            simpa only [hr0] using hz)
        refine ⟨⟨b+u,add_nonneg hb hu.1,by linarith [hu.2]⟩,?_⟩
        exact (E.compact_edge_upper ⟨u,hu⟩).trans
          (congrArg (fun q ↦ (G q).1) he.symm)
      · by_cases hu0 : u=0
        · have he : z=translatedStripBottom (v:=v) hh ⟨r,hr⟩ :=
            Subtype.ext (by
              change z.1 = flatShearedPoint v r 0
              simpa only [hu0] using hz)
          have hmap : (G z).1 = (F (translatedStripTop hb (⟨r,hr⟩ : NNReal))).1 :=
            (congrArg (fun q ↦ (G q).1) he).trans (hseam (⟨r,hr⟩ : NNReal))
          exact hmap.symm ▸ hOld (translatedStripTop hb (⟨r,hr⟩ : NNReal))
            (hmap ▸ hqfront)
        · have he : z=⟨flatShearedPoint v r u,r,hr,u,hu,rfl⟩ := Subtype.ext hz
          have hiQ : (G z).1∈interior Q := by
            rw [he]
            exact hGinterior ⟨r,hr⟩ (by
              change (0 : ℝ) < r
              exact lt_of_le_of_ne hr (Ne.symm hr0)) ⟨u,hu⟩
              (lt_of_le_of_ne hu.1 (Ne.symm hu0))
          exact (hqfront.2 (interior_mono hQP hiQ)).elim
  · rintro (⟨r,rfl⟩ | ⟨u,rfl⟩)
    · refine ⟨mem_range_self _,?_⟩
      change (E.map (translatedStripBottom (add_nonneg hb hh) r)).1 ∈ frontier P
      rw [E.bottom]
      exact hFbottom r
    · refine ⟨mem_range_self _,?_⟩
      change (E.map (translatedStripEdge u)).1 ∈ frontier P
      by_cases hub : u.1≤b
      · have he : translatedStripEdge (v:=v) u=translatedStripLowerInclusion hh
            (translatedStripEdge ⟨u.1,u.2.1,hub⟩) := Subtype.ext rfl
        rw [he,E.lower]
        exact hFedge _
      · have hbu : b≤u.1 := (lt_of_not_ge hub).le
        let w : Icc (0:ℝ) h := ⟨u.1-b,sub_nonneg.mpr hbu,by linarith [u.2.2]⟩
        have he : translatedStripEdge (v:=v) u=translatedStripUpperInclusion hb
            (translatedStripEdge w) := by
          apply Subtype.ext
          dsimp [translatedStripEdge,translatedStripUpperInclusion,flatShearedPoint,w]
          simp only [Complex.ofReal_sub]
          ring
        rw [he,E.upper]
        exact hGedgeP w

/-- If both pieces use the same prescribed boundary arclength, the merged map
uses it on the entire enlarged compact edge, including the seam endpoint. -/
theorem compact_edge_eq_prescribed
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ}
    {v : ℂ} {b h : ℝ} {hb : 0≤b} {hh : 0≤h}
    {F : flatShearedStrip v b → P} {G : flatShearedStrip v h → Q}
    (E : PointTranslatedStripSeamGluing a y P Q v b h hb hh F G)
    (σ : Icc (0:ℝ) (b+h) → ℂ)
    (hFedge : ∀ u : Icc (0:ℝ) b,(F (translatedStripEdge u)).1=
      σ ⟨u.1,u.2.1,u.2.2.trans (le_add_of_nonneg_right hh)⟩)
    (hGedge : ∀ u : Icc (0:ℝ) h,(G (translatedStripEdge u)).1=
      σ ⟨b+u.1,add_nonneg hb u.2.1,by linarith [u.2.2]⟩) :
    ∀ u : Icc (0:ℝ) (b+h),(E.map (translatedStripEdge u)).1=σ u := by
  intro u
  by_cases hub : u.1≤b
  · exact (congrArg Subtype.val (E.compact_edge_lower ⟨u.1,u.2.1,hub⟩)).trans (hFedge _)
  · have hbu : b≤u.1 := (lt_of_not_ge hub).le
    let w : Icc (0:ℝ) h := ⟨u.1-b,sub_nonneg.mpr hbu,by linarith [u.2.2]⟩
    have he : (⟨b+w.1,add_nonneg hb w.2.1,by linarith [w.2.2]⟩ : Icc (0:ℝ) (b+h))=u := by
      apply Subtype.ext
      dsimp [w]
      ring
    have ht := (E.compact_edge_upper w).trans (hGedge w)
    simpa only [he] using ht

end PointTranslatedStripSeamGluing
end RepulsiveCoulomb
