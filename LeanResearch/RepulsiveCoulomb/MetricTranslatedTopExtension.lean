import LeanResearch.RepulsiveCoulomb.TranslatedSupportingHalfplane
import LeanResearch.RepulsiveCoulomb.MetricInteriorSupportedPatchExtension
import LeanResearch.RepulsiveCoulomb.MetricShearedTopExtension

/-! ISOLATED SOURCE-ONLY DRAFT, 2026-10-03. Construct the mixed compact-top
extension. Its left endpoint uses the real old-boundary interval and a retained
halfdisk; every other top point uses a genuine full disk. The two classes are
kept separate. All patch maps and all overlap identities are outputs. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Compact-edge source point with its actual transverse arclength. -/
def shearedCompactEdgePoint {v : ℂ} {R s : ℝ} (hR : 0 ≤ R) (u : Icc (0 : ℝ) s) :
    flatShearedRectangle v R s :=
  ⟨flatShearedPoint v 0 u.1, 0, ⟨le_rfl, hR⟩, u.1, u.2, rfl⟩

/-- A whole relative patch at the top-left endpoint, aligned to the actual
adjacent old boundary beyond that endpoint. The extended boundary interval is
one-dimensional original geometry, not a continued strip or patch hypothesis. -/
theorem exists_translated_compact_edge_patch {Y : Type*} [MetricSpace Y]
    {stripAngle R s ell : ℝ} (hR : 0 ≤ R) (hs : 0 < s) (hsell : s < ell)
    (f : flatShearedRectangle (conePhase stripAngle) R s → Y) (hf : Isometry f)
    (edge : Icc (0 : ℝ) ell → Y) (hedge : Isometry edge)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩)
    (C : MetricFlatHalfDiskChart Y
      (f (shearedCompactEdgePoint hR ⟨s, hs.le, le_rfl⟩))) :
    ∃ B : ℝ, 0 < B ∧
      ∃ e : supportedFlatPatch (translatedSupportingHalfplane stripAngle)
          (flatShearedPoint (conePhase stripAngle) 0 s) B ≃ᵢ
          ball (f (shearedCompactEdgePoint hR ⟨s, hs.le, le_rfl⟩)) B,
        ∀ x : flatShearedRectangle (conePhase stripAngle) R s,
          ∀ hx : x.1 ∈ supportedFlatPatch (translatedSupportingHalfplane stripAngle)
            (flatShearedPoint (conePhase stripAngle) 0 s) B,
            (e ⟨x.1, hx⟩).1 = f x := by
  let q := shearedCompactEdgePoint (v := conePhase stripAngle) hR ⟨s, hs.le, le_rfl⟩
  let L := min (s / 2) (min ((ell - s) / 2) (C.radius / 2))
  have hL : 0 < L := lt_min (half_pos hs)
    (lt_min (half_pos (sub_pos.mpr hsell)) (half_pos C.radius_pos))
  have hLs : L < s := (min_le_left _ _).trans_lt (half_lt_self hs)
  have hLell : L < ell - s :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self (sub_pos.mpr hsell))
  have hLC : L < C.radius :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self C.radius_pos)
  let τ : Icc (-L) L → Icc (0 : ℝ) ell := fun t ↦
    ⟨s - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro t u
    change |(s - t.1) - (s - u.1)| = |t.1 - u.1|
    rw [show (s - t.1) - (s - u.1) = -(t.1 - u.1) by ring, abs_neg]
  have hτ0 : τ (complexSymmetricIntervalZero hL) = ⟨s, hs.le, hsell.le⟩ := by
    apply Subtype.ext
    simp [τ, complexSymmetricIntervalZero]
  let b : Icc (-L) L := ⟨L, by constructor <;> linarith⟩
  let u₁ : Icc (0 : ℝ) s := ⟨s - L, by constructor <;> linarith⟩
  let q₁ := shearedCompactEdgePoint (v := conePhase stripAngle) hR u₁
  have hρ0 : (edge ∘ τ) (complexSymmetricIntervalZero hL) = f q := by
    change edge (τ (complexSymmetricIntervalZero hL)) = f q
    rw [hτ0]
    exact (hold ⟨s, hs.le, le_rfl⟩).symm
  have hρb : (edge ∘ τ) b = f q₁ := by
    exact (hold u₁).symm
  have hq : translatedSupportingRigid stripAngle s q.1 = 0 := translatedSupportingRigid_top_origin stripAngle s
  have hq₁ : translatedSupportingRigid stripAngle s q₁.1 = (b.1 : ℂ) := by
    change translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) 0 (s - L)) = (L : ℂ)
    rw [translatedSupportingRigid_sheared]
    simp
  have hpatch := exists_relative_halfDisk_patch_extension f hf q q₁
    (translatedSupportingRigid stripAngle s) hq C hL hLC (edge ∘ τ) (hedge.comp hτ)
    hρ0 b hL.ne' hq₁ hρb
  rw [← translatedSupportingHalfplane_eq_rigid stripAngle s] at hpatch
  obtain ⟨e, he⟩ := hpatch
  exact ⟨C.radius, C.radius_pos, e, he⟩

/-- Positive compact-top continuation from genuine charts and the actual
adjacent edge. The source support is a halfplane, and the singular case r = 0
is treated with a relative halfdisk rather than an ambient disk. -/
theorem exists_translated_top_local_extension {Y : Type*} [MetricSpace Y]
    {stripAngle R s delta ell : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    (hR : 0 < R) (hs : 0 < s) (hsdelta : s < delta) (hsell : s < ell)
    (f : flatShearedRectangle (conePhase stripAngle) R s → Y) (hf : Isometry f)
    (edge : Icc (0 : ℝ) ell → Y) (hedge : Isometry edge)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩)
    (C : MetricFlatHalfDiskChart Y
      (f (shearedCompactEdgePoint hR.le ⟨s, hs.le, le_rfl⟩)))
    (hregular : ∀ r : Icc (0 : ℝ) R, 0 < r.1 →
      Nonempty (MetricFlatDiskChart Y
        (f (shearedTopPoint (conePhase stripAngle) R s hs.le r)))) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧
      ∃ G : interior (flatShearedRectangle (conePhase stripAngle) R (s + h)) → Y,
        (∀ x : interior (flatShearedRectangle (conePhase stripAngle) R s),
          ∀ hx : x.1 ∈ interior (flatShearedRectangle (conePhase stripAngle) R (s + h)),
            G ⟨x.1, hx⟩ = f ⟨x.1, interior_subset x.2⟩) ∧
        ∀ p, ∃ V : Set (interior (flatShearedRectangle (conePhase stripAngle) R (s + h))),
          IsOpen V ∧ p ∈ V ∧
          ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z := by
  let K := flatShearedRectangle (conePhase stripAngle) R s
  let H := translatedSupportingHalfplane stripAngle
  let q := shearedTopPoint (conePhase stripAngle) R s hs.le
  have hvi : (conePhase stripAngle).im ≠ 0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  have hpatch (r : Icc (0 : ℝ) R) : ∃ B : ℝ, 0 < B ∧
      ∃ e : supportedFlatPatch H (q r).1 B ≃ᵢ ball (f (q r)) B,
        ∀ x : K, ∀ hx : x.1 ∈ supportedFlatPatch H (q r).1 B,
          (e ⟨x.1, hx⟩).1 = f x := by
    by_cases hr : r.1 = 0
    · have hr0 : r = ⟨0, le_rfl, hR.le⟩ := Subtype.ext hr
      subst r
      exact exists_translated_compact_edge_patch hR.le hs hsell f hf edge hedge hold C
    · have hrpos : 0 < r.1 := lt_of_le_of_ne r.2.1 (Ne.symm hr)
      obtain ⟨D⟩ := hregular r hrpos
      exact exists_interior_supported_patch_extension (flatShearedRectangle_convex _ _ _)
        (flatShearedRectangle_interior_nonempty hvi hR hs) f hf (q r)
        (translatedSupportingHalfplane_interior_positive stripAngle_pos stripAngle_lt_pi hrpos s) D
  choose B hB e he using hpatch
  exact exists_sheared_top_local_extension (conePhase_norm stripAngle) hvi hR hs hsdelta
    (translatedSupportingHalfplane_convex stripAngle)
    (flatShearedRectangle_subset_translatedSupportingHalfplane stripAngle_pos stripAngle_lt_pi R delta)
    f hf B hB e he

end RepulsiveCoulomb
