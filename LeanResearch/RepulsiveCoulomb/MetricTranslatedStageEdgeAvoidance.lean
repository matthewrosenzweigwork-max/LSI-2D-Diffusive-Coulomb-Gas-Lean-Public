import LeanResearch.RepulsiveCoulomb.MetricTranslatedPrescribedEdgeNoReturn
import LeanResearch.RepulsiveCoulomb.PointTranslatedLongitudinalExtension

/-! SOURCE-ONLY ASSEMBLY AFTER THE FROZEN PRODUCER SUBSET. Derive all easy
edge exclusions from the actual finite rectangle. These are not assumed
boundary nonreturn certificates. The only remaining boundary is the forward
old end, which is ruled out by the separate retained parallel cap theorem. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem metric_translated_stage_avoids_bottom {Y : Type*} [MetricSpace Y]
    {stripAngle R s : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hR : 0 < R) (hs : 0 ≤ s)
    (ρ : NNReal → Y) (hρ : Isometry ρ)
    (f : flatShearedRectangle (conePhase stripAngle) R s → Y) (hf : Isometry f)
    (hbottom : ∀ r : Icc (0 : ℝ) R, f (shearedBottomPoint hs r) = ρ ⟨r.1, r.2.1⟩)
    (r : Icc (0 : ℝ) R) (u : Icc (0 : ℝ) s) (hu : 0 < u.1) :
    f ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩ ∉ range ρ := by
  let x₀ := shearedBottomPoint (v := conePhase stripAngle) hs (⟨0, le_rfl, hR.le⟩ : Icc (0 : ℝ) R)
  let x₁ := shearedBottomPoint (v := conePhase stripAngle) hs (⟨R, hR.le, le_rfl⟩ : Icc (0 : ℝ) R)
  let z : flatShearedRectangle (conePhase stripAngle) R s :=
    ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩
  have hz : ((IsometryEquiv.refl ℂ) z.1).im ≠ 0 := by
    change (flatShearedPoint (conePhase stripAngle) r.1 u.1).im ≠ 0
    have hpos := mul_pos hu (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi)
    simpa [flatShearedPoint, Complex.mul_im, conePhase_im] using hpos.ne'
  exact metric_flat_patch_no_prescribed_edge_return ρ hρ f hf
    (IsometryEquiv.refl ℂ) (0 : NNReal) (⟨R, hR.le⟩ : NNReal) hR.ne
    x₀ x₁ (by
      change flatShearedPoint (conePhase stripAngle) 0 0 = (0 : ℂ)
      simp [flatShearedPoint]) (by
      change flatShearedPoint (conePhase stripAngle) R 0 = (R : ℂ)
      simp [flatShearedPoint])
    (hbottom ⟨0, le_rfl, hR.le⟩) (hbottom ⟨R, hR.le, le_rfl⟩) z hz

theorem metric_translated_stage_avoids_compact_edge {Y : Type*} [MetricSpace Y]
    {stripAngle R s : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hR : 0 ≤ R) (hs : 0 < s)
    (edge : Icc (0 : ℝ) s → Y) (hedge : Isometry edge)
    (f : flatShearedRectangle (conePhase stripAngle) R s → Y) (hf : Isometry f)
    (hold : ∀ u : Icc (0 : ℝ) s, f (shearedCompactEdgePoint hR u) = edge u)
    (r : Icc (0 : ℝ) R) (hr : 0 < r.1) (u : Icc (0 : ℝ) s) :
    f ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩ ∉ range edge := by
  let flip : Icc (-s) (0 : ℝ) → Icc (0 : ℝ) s := fun t ↦ ⟨-t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  have hflip : Isometry flip := by
    apply Isometry.of_dist_eq
    intro t w
    change dist (-t.1) (-w.1) = dist t.1 w.1
    exact dist_neg_neg _ _
  let ρ := edge ∘ flip
  have hρ : Isometry ρ := hedge.comp hflip
  let x₀ := shearedCompactEdgePoint (v := conePhase stripAngle) hR (⟨0, le_rfl, hs.le⟩ : Icc (0 : ℝ) s)
  let x₁ := shearedCompactEdgePoint (v := conePhase stripAngle) hR (⟨s, hs.le, le_rfl⟩ : Icc (0 : ℝ) s)
  let z : flatShearedRectangle (conePhase stripAngle) R s :=
    ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩
  have hc : translatedSupportingRigid stripAngle 0 x₀.1 = ((0 : ℝ) : ℂ) := by
    rw [show x₀.1 = flatShearedPoint (conePhase stripAngle) 0 0 from rfl, translatedSupportingRigid_sheared]
    simp
  have hd : translatedSupportingRigid stripAngle 0 x₁.1 = ((-s : ℝ) : ℂ) := by
    rw [show x₁.1 = flatShearedPoint (conePhase stripAngle) 0 s from rfl, translatedSupportingRigid_sheared]
    simp
  have hz : (translatedSupportingRigid stripAngle 0 z.1).im ≠ 0 := by
    rw [show z.1 = flatShearedPoint (conePhase stripAngle) r.1 u.1 from rfl,
      translatedSupportingRigid_sheared_im]
    exact (mul_pos hr (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi)).ne'
  have hno := metric_flat_patch_no_prescribed_edge_return ρ hρ f hf
    (translatedSupportingRigid stripAngle 0) (⟨0, by constructor <;> linarith⟩ : Icc (-s) (0 : ℝ))
    (⟨-s, le_rfl, by linarith⟩ : Icc (-s) (0 : ℝ)) (by linarith : (0 : ℝ) ≠ -s)
    x₀ x₁ hc hd (by simpa [ρ, flip] using hold ⟨0, le_rfl, hs.le⟩)
    (by simpa [ρ, flip] using hold ⟨s, hs.le, le_rfl⟩) z hz
  rintro ⟨t, ht⟩
  apply hno
  refine ⟨⟨-t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩, ?_⟩
  simpa [ρ, flip] using ht

end RepulsiveCoulomb
