module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripOldEdgeFullness

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Classify actual removed old-boundary points
using the exact contact equality, then instantiate the constructed apex and
edge fullness results. No local filling assertion is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_removed_boundary_local_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P =
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (hcharts : ∀ p∈frontier P,∃ C : PointRetainedConeNeighborhood a y P p,C.Admissible)
    (q : flatShearedStrip (conePhase stripAngle) b)
    (hqfront : (F q).1∈frontier P)
    (hqtop : (F q).1∉range (fun r ↦ (F (translatedStripTop hb.le r)).1)) :
    ∃ ρ : ℝ,0<ρ ∧ ∀ z∈P,
      (pointSmoothConformalEDist a y z (F q).1).toReal≤ρ → z∈range (fun x ↦ (F x).1) := by
  have hbottom (r : NNReal) : (F (translatedStripBottom hb.le r)).1∈frontier P := by
    have hm : (F (translatedStripBottom hb.le r)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inl ⟨r,rfl⟩
    exact hm.2
  have hedge (u : Icc (0:ℝ) b) : (F (translatedStripEdge u)).1∈frontier P := by
    have hm : (F (translatedStripEdge u)).1∈range (fun x ↦ (F x).1) ∩ frontier P :=
      hcontact.symm ▸ Or.inr ⟨u,rfl⟩
    exact hm.2
  have hapex : ∃ ρ : ℝ,0<ρ ∧ ∀ z∈P,
      (pointSmoothConformalEDist a y z (F (translatedStripBottom hb.le 0)).1).toReal≤ρ →
        z∈range (fun x ↦ (F x).1) := by
    obtain ⟨C,hC⟩:=hcharts _ (hbottom 0)
    exact (pointTranslatedStrip_apex_width_and_local_fullness ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact C hC).2.2
  have hc : (F q).1 ∈
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1) := by
    rw [← hcontact]
    exact ⟨⟨q, rfl⟩, hqfront⟩
  rcases hc with ⟨r,hr⟩ | ⟨u,hu⟩
  · change (F (translatedStripBottom hb.le r)).1 = (F q).1 at hr
    by_cases hr0 : r=0
    · subst r
      simpa only [hr] using hapex
    · have hrpos : 0<r:=lt_of_le_of_ne (show (0 : NNReal) ≤ r from r.2) (Ne.symm hr0)
      obtain ⟨C,hC⟩:=hcharts _ (hbottom r)
      have hf:=(pointTranslatedStrip_bottom_width_and_local_fullness ha y stripAngle_pos stripAngle_lt_pi hb
        F hF hbottom r hrpos C hC).2
      simpa only [hr] using hf
  · change (F (translatedStripEdge u)).1 = (F q).1 at hu
    by_cases hu0 : u.1=0
    · have he : translatedStripEdge (v := conePhase stripAngle) u=translatedStripBottom hb.le 0 := by
        apply Subtype.ext
        change flatShearedPoint (conePhase stripAngle) 0 u.1 =
          flatShearedPoint (conePhase stripAngle) 0 0
        rw [hu0]
      have hpoint : (F (translatedStripBottom hb.le 0)).1=(F q).1 := by rwa [he] at hu
      simpa only [hpoint] using hapex
    · have hub : u.1<b := lt_of_le_of_ne u.2.2 (by
        intro hub
        have he : translatedStripEdge (v := conePhase stripAngle) u=translatedStripTop hb.le 0 := by
          apply Subtype.ext
          change flatShearedPoint (conePhase stripAngle) 0 u.1=flatShearedPoint (conePhase stripAngle) 0 b
          rw [hub]
        exact hqtop ⟨0,by simpa only [he] using hu⟩)
      have hupos : 0<u.1:=lt_of_le_of_ne u.2.1 (Ne.symm hu0)
      obtain ⟨C,hC⟩:=hcharts _ (hedge u)
      have hf:=(pointTranslatedStrip_edge_width_and_local_fullness ha y stripAngle_pos stripAngle_lt_pi
        F hF hedge u hupos hub C hC).2
      simpa only [hu] using hf

end RepulsiveCoulomb
