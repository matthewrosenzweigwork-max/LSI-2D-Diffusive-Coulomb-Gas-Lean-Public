import LeanResearch.RepulsiveCoulomb.PointTranslatedStripOldEdgeFullness

/-! SOURCE-ONLY, UNCOMPILED. If the actual free top lies on the old frontier,
its positive points fill P locally. Both source diameter endpoints are genuine
old-frontier points. No target width or relative-openness premise is supplied. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointTranslatedStrip_top_boundary_local_fullness
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle b : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hb : 0 < b)
    (F : flatShearedStrip (conePhase stripAngle) b → P)
    (hF : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (htop : ∀ t : NNReal, (F (translatedStripTop hb.le t)).1 ∈ frontier P)
    (t : NNReal) (ht : 0 < t)
    (C : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb.le t)).1)
    (hC : C.Admissible) :
    C.flatPhysicalWidth = Real.pi ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ P,
      (pointSmoothConformalEDist a y z (F (translatedStripTop hb.le t)).1).toReal ≤ ρ →
        z ∈ range (fun x ↦ (F x).1) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi
  let L := min b (t : ℝ) * Real.sin stripAngle / 2
  obtain ⟨hL, hLb, hLt⟩ := translatedStripHorizontal_radius stripAngle_pos stripAngle_lt_pi hb ht
  let J := translatedStripTopSource hs hLb hLt
  have hJ0 : J (flatLinkSectorDiskApex Real.pi_pos.le hL.le) =
      translatedStripTop hb.le t := by
    apply Subtype.ext
    exact translatedStripTopRigid_zero stripAngle b t
  have hfront (r : ℝ) (hr : r ∈ Icc (0 : ℝ) L) :
      (F (J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 0))).1 ∈ frontier P ∧
      (F (J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 1))).1 ∈ frontier P := by
    have hrt : r ≤ t := hr.2.trans (hLt.trans
      (mul_le_of_le_one_right t.2 (Real.sin_le_one stripAngle)))
    let rm : NNReal := ⟨(t : ℝ) - r, sub_nonneg.mpr hrt⟩
    let rp : NNReal := ⟨(t : ℝ) + r, add_nonneg t.2 hr.1⟩
    have he0 : J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 0) =
        translatedStripTop hb.le rm := by
      apply Subtype.ext
      change translatedStripTopRigid stripAngle b t (sectorPolar r (Real.pi * (0 : unitInterval).1)) =
        flatShearedPoint (conePhase stripAngle) ((t : ℝ) - r) b
      simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero,
        translatedStripTopRigid_edge_zero]
    have he1 : J (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl r hr 1) =
        translatedStripTop hb.le rp := by
      apply Subtype.ext
      change translatedStripTopRigid stripAngle b t (sectorPolar r (Real.pi * (1 : unitInterval).1)) =
        flatShearedPoint (conePhase stripAngle) ((t : ℝ) + r) b
      simp only [show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one,
        translatedStripTopRigid_edge_pi]
    exact ⟨he0.symm ▸ htop rm, he1.symm ▸ htop rp⟩
  exact pointFlatBoundaryPatch_fullness ha y F hF Real.pi_pos le_rfl hL J
    (translatedStripTopSource_isometry hs hLb hLt)
    (translatedStripTop hb.le t) hJ0 hfront C hC

end RepulsiveCoulomb
