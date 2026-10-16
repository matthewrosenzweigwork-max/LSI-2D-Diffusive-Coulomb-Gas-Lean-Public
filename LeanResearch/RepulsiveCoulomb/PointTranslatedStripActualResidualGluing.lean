module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripSeamBoundary
public import LeanResearch.RepulsiveCoulomb.PointActualTranslatedStripIteration

@[expose] public section

/-! SOURCE ONLY, UNCOMPILED. Apply seam gluing directly to the output of the
actual translated-strip residual construction. The residual closure, cover,
closedness and frontier relation are not fresh caller certificates. They are
read from the genuine geometric cut output. The new uniform strip itself must
be constructed separately; this file does not claim maximal width or contact. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The actual residual state and an actual newly constructed uniform strip
produce the enlarged old-region strip with all-pairs ambient isometry and exact
old-boundary contact. In particular, a cut output is not mistaken for an
extension: the merged map is constructed by the seam theorem. -/
theorem pointTranslatedStrip_glue_actual_residual
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {stripAngle b h : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi)
    (hb : 0≤b) (hh : 0≤h)
    (F : flatShearedStrip (conePhase stripAngle) b → P)
    (G : flatShearedStrip (conePhase stripAngle) h → Q)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hG : ∀ x z,(pointSmoothConformalEDist a y (G x).1 (G z).1).toReal=dist x z)
    (hconv : PointGeodesicallyConvex a y P)
    (hseam : ∀ r,(G (translatedStripBottom hh r)).1=(F (translatedStripTop hb r)).1)
    (hFcontact : range (fun x ↦ (F x).1)∩frontier P=
      range (fun r ↦ (F (translatedStripBottom hb r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    {p : ℂ} {ν μ α : ℂ→₀ℝ}
    {Cz : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb 0)).1}
    (K : PointTranslatedStripIterationOutput a y P (range (fun x ↦ (F x).1)) Q
      (fun r ↦ (F (translatedStripTop hb r)).1) p ν μ α (Real.pi-stripAngle) Cz)
    (hGedge : ∀ u,(G (translatedStripEdge u)).1∈frontier Q)
    (hGinterior : ∀ r : NNReal,0<r → ∀ u : Icc (0:ℝ) h,0<u.1 →
      (G ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1∈interior Q) :
    ∃ E : PointTranslatedStripSeamGluing a y P Q (conePhase stripAngle) b h hb hh F G,
      range (fun x ↦ (E.map x).1)∩frontier P=
        range (fun r ↦ (E.map (translatedStripBottom (add_nonneg hb hh) r)).1) ∪
        range (fun u ↦ (E.map (translatedStripEdge u)).1) := by
  have hvi : (conePhase stripAngle).im≠0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  obtain ⟨E⟩ := pointTranslatedStrip_glue_successive ha y hvi hb hh F G hF hG hconv
    K.state.isClosed K.literal_difference hseam
  have hfront : frontier Q ⊆
      range (fun r ↦ (F (translatedStripTop hb r)).1) ∪ frontier P := by
    rw [K.frontier_eq]
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · rw [K.old_forward_range] at hz
      rcases hz with hz | hz
      · left
        exact ⟨0,hz.symm⟩
      · exact Or.inr hz.1
  exact ⟨E,PointTranslatedStripSeamGluing.exact_old_boundary_contact ha y hvi hb hh F G E hG hseam K.subset_old
    hFcontact hGedge hfront hGinterior⟩

end RepulsiveCoulomb
