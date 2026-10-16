import LeanResearch.RepulsiveCoulomb.MetricTranslatedTopExtension
import LeanResearch.RepulsiveCoulomb.FlatLinkSectorDisk

/-! ISOLATED SOURCE-ONLY DRAFT. Construct the literal bounded halfdisk used
by the retained parallel-return theorem from the actual relative patch.
Its backward-old-edge and outgoing-parallel traces are proved by rigid source
coordinates and old-map agreement. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def translatedParallelDirection {stripAngle : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) : unitInterval :=
  ⟨(Real.pi - stripAngle) / Real.pi, (div_pos (sub_pos.mpr stripAngle_lt_pi) Real.pi_pos).le,
    ((div_lt_one Real.pi_pos).mpr (by linarith)).le⟩

theorem translatedSupportingRigid_parallel (stripAngle s r : ℝ) :
    translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) r s) =
      sectorPolar r (Real.pi - stripAngle) := by
  rw [translatedSupportingRigid_sheared]
  apply Complex.ext <;>
    simp [sectorPolar_re, sectorPolar_im, conePhase_re, conePhase_im,
      Complex.mul_re, Complex.mul_im, Real.cos_pi_sub, Real.sin_pi_sub]

theorem exists_relative_patch_closed_halfDisk {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (f : K → Y) (q : K) (E : ℂ ≃ᵢ ℂ) (hq : E q.1 = 0)
    {B L : ℝ} (hL : 0 < L) (hLB : L < B)
    (e : supportedFlatPatch (rigidUpperHalfplane E) q.1 B ≃ᵢ ball (f q) B)
    (hold : ∀ x : K, ∀ hx : x.1 ∈ supportedFlatPatch (rigidUpperHalfplane E) q.1 B,
      (e ⟨x.1, hx⟩).1 = f x) :
    ∃ g : flatLinkSectorDisk Real.pi L → Y, Isometry g ∧
      g (flatLinkSectorDiskApex Real.pi_pos.le hL.le) = f q ∧
      ∀ z : flatLinkSectorDisk Real.pi L, ∀ x : K, E x.1 = z.1 → g z = f x := by
  let A := rigidUpperHalfDiskEquiv E hq B
  have hupper (z : flatLinkSectorDisk Real.pi L) : z.1 ∈ flatUpperDisk B :=
    ⟨z.2.2.trans_lt hLB, Complex.arg_nonneg_iff.mp z.2.1.1⟩
  let incl : flatLinkSectorDisk Real.pi L → flatUpperDisk B := fun z ↦ ⟨z.1, hupper z⟩
  have hincl : Isometry incl := fun _ _ ↦ rfl
  let g : flatLinkSectorDisk Real.pi L → Y := fun z ↦ (e (A.symm (incl z))).1
  have hg : Isometry g := by
    apply Isometry.of_dist_eq
    intro z w
    exact ((e.isometry.comp A.symm.isometry).comp hincl).dist_eq z w
  have hagree (z : flatLinkSectorDisk Real.pi L) (x : K) (hx : E x.1 = z.1) : g z = f x := by
    have hxmem : x.1 ∈ supportedFlatPatch (rigidUpperHalfplane E) q.1 B := by
      constructor
      · change dist x.1 q.1 < B
        rw [← E.dist_eq, hx, hq, dist_zero_right]
        exact (hupper z).1
      · change 0 ≤ (E x.1).im
        rw [hx]
        exact (hupper z).2
    have heq : A.symm (incl z) = ⟨x.1, hxmem⟩ := by
      apply A.injective
      rw [A.apply_symm_apply]
      apply Subtype.ext
      exact hx.symm
    change (e (A.symm (incl z))).1 = f x
    rw [heq]
    exact hold x hxmem
  exact ⟨g, hg, hagree _ q hq, hagree⟩

/-- Actual isometric halfdisk at the compact-edge endpoint. It already
contains both germs required by the parallel-return obstruction. -/
theorem exists_translated_source_halfDisk {Y : Type*} [MetricSpace Y]
    {stripAngle R s ell : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    (hR : 0 < R) (hs : 0 < s) (hsell : s < ell)
    (f : flatShearedRectangle (conePhase stripAngle) R s → Y) (hf : Isometry f)
    (edge : Icc (0 : ℝ) ell → Y) (hedge : Isometry edge)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩)
    (C : MetricFlatHalfDiskChart Y
      (f (shearedCompactEdgePoint hR.le ⟨s, hs.le, le_rfl⟩))) :
    ∃ L : ℝ, ∃ hL : 0 < L, L < R ∧ L < s ∧
      ∃ g : flatLinkSectorDisk Real.pi L → Y, Isometry g ∧
        g (flatLinkSectorDiskApex Real.pi_pos.le hL.le) =
          f (shearedCompactEdgePoint hR.le ⟨s, hs.le, le_rfl⟩) ∧
        (∀ t : ℝ, ∀ ht : 0 ≤ t, ∀ htL : t ≤ L,
          ∃ hts : s - t ∈ Icc (0 : ℝ) ell,
            g (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨ht, htL⟩ 0) = edge ⟨s-t, hts⟩) ∧
        ∀ t : ℝ, ∀ ht : 0 ≤ t, ∀ htL : t ≤ L,
          ∃ htR : t ∈ Icc (0 : ℝ) R,
            g (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨ht, htL⟩
              (translatedParallelDirection stripAngle_pos stripAngle_lt_pi)) =
                f (shearedTopPoint (conePhase stripAngle) R s hs.le ⟨t, htR⟩) := by
  let q := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le ⟨s, hs.le, le_rfl⟩
  have hpatch := exists_translated_compact_edge_patch hR.le hs hsell f hf edge hedge hold C
  rw [translatedSupportingHalfplane_eq_rigid stripAngle s] at hpatch
  obtain ⟨B, hB, e, he⟩ := hpatch
  let L := min B (min R s) / 2
  have hL : 0 < L := half_pos (lt_min hB (lt_min hR hs))
  have hLm : L < min B (min R s) := half_lt_self (lt_min hB (lt_min hR hs))
  have hLB : L < B := hLm.trans_le (min_le_left _ _)
  have hLR : L < R := hLm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hLs : L < s := hLm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨g, hg, hg0, hgagree⟩ := exists_relative_patch_closed_halfDisk f q
    (translatedSupportingRigid stripAngle s) (translatedSupportingRigid_top_origin stripAngle s) hL hLB e he
  refine ⟨L, hL, hLR, hLs, g, hg, hg0, ?_, ?_⟩
  · intro t ht htL
    have hts : s - t ∈ Icc (0 : ℝ) s := ⟨by linarith, sub_le_self _ ht⟩
    let x := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le ⟨s-t, hts⟩
    have hx : translatedSupportingRigid stripAngle s x.1 =
        (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨ht, htL⟩ 0).1 := by
      change translatedSupportingRigid stripAngle s
        (flatShearedPoint (conePhase stripAngle) 0 (s-t)) =
          sectorPolar t (Real.pi * (0 : unitInterval).1)
      rw [translatedSupportingRigid_sheared]
      simp [sectorPolar, conePhase]
    exact ⟨⟨hts.1, hts.2.trans hsell.le⟩, (hgagree _ x hx).trans (hold ⟨s-t, hts⟩)⟩
  · intro t ht htL
    have htR : t ∈ Icc (0 : ℝ) R := ⟨ht, htL.trans hLR.le⟩
    let x := shearedTopPoint (conePhase stripAngle) R s hs.le ⟨t, htR⟩
    have hangle : Real.pi * (translatedParallelDirection stripAngle_pos stripAngle_lt_pi).1 = Real.pi - stripAngle := by
      change Real.pi * ((Real.pi - stripAngle) / Real.pi) = Real.pi - stripAngle
      exact mul_div_cancel₀ _ Real.pi_ne_zero
    have hx : translatedSupportingRigid stripAngle s x.1 =
        (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨ht, htL⟩
          (translatedParallelDirection stripAngle_pos stripAngle_lt_pi)).1 := by
      change translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) t s) =
        sectorPolar t (Real.pi * (translatedParallelDirection stripAngle_pos stripAngle_lt_pi).1)
      rw [translatedSupportingRigid_parallel, hangle]
    exact ⟨htR, hgagree _ x hx⟩

end RepulsiveCoulomb
