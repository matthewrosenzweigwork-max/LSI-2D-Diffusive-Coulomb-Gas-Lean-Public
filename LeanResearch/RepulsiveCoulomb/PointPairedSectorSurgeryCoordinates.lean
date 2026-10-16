import LeanResearch.RepulsiveCoulomb.PointActualSectorLocalCoordinates
import LeanResearch.RepulsiveCoulomb.PointIncidentSectorSourcePatch

/-! SOURCE-ONLY, UNCOMPILED. Construct the old directed source patch and new
inverse coordinates as one pair. Their exact seam formula uses the same
original sector coordinates. Thus no independent choice of halfdisk can
silently reverse the endpoint labels used by the finite cyclic order. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

structure PointPairedSectorSurgeryCoordinates
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) (p : ℂ) (c : ℝ) where
  old : EuclideanSectorDiskPatch S.beta
  new : EuclideanSectorDiskPatch (c * S.beta)
  center : S.map (old.inclusion (flatLinkSectorDiskApex old.angle_pos.le old.radius_pos.le)) = p
  old_angle : old.angle = if p = S.apex then S.beta else Real.pi
  new_angle : new.angle = if p = S.apex then c * S.beta else Real.pi
  seam : ∀ r : ℝ, 0 ≤ r → r ≤ old.radius → r ≤ new.radius →
    ∀ t : unitInterval, t = 0 ∨ t = 1 →
      sectorAngularMap c (old.placement (sectorPolar r (old.angle * t.1))) =
        new.placement (sectorPolar r (new.angle * t.1))

namespace PointPairedSectorSurgeryCoordinates
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ} {c : ℝ}

/-- This is the precise old patch whose derived Boolean is to be passed to
the finite cell construction and to the new target placement. -/
def sourcePatch (B : PointPairedSectorSurgeryCoordinates S p c) :
    PointIncidentSectorSourcePatch S p where
  angle := B.old.angle
  angle_pos := B.old.angle_pos
  angle_le_pi := B.old.angle_le_pi
  radius := B.old.radius
  radius_pos := B.old.radius_pos
  sourceMap := B.old.inclusion
  isometry := B.old.inclusion_isometry
  center := B.center
  local_range := by
    intro q hq
    rw [B.old.inclusion_range]
    exact hq
  interior := fun x hx _ hxR ↦ B.old.inclusion_mem_interior x hx hxR
  angle_eq := B.old_angle

/-- Both physical inverse branches identify exactly the same old seam point
at every common arclength. This is before applying their ordered placements. -/
theorem inverse_seam (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hrold : r ≤ B.old.radius) (hrnew : r ≤ B.new.radius)
    (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    (S.localInverse ha hc hc1 B.new
      (flatLinkSectorDiskPoint B.new.angle_pos.le B.new.angle_le_pi r ⟨hr, hrnew⟩ t)).1 =
      B.sourcePatch.map
        (flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r ⟨hr, hrold⟩ t) := by
  let w := flatLinkSectorDiskPoint B.new.angle_pos.le B.new.angle_le_pi r ⟨hr, hrnew⟩ t
  let x := flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi r ⟨hr, hrold⟩ t
  let H := pointActualSectorContractionChart ha S hc hc1
  have heq : S.localInverse ha hc hc1 B.new w =
      ⟨S.map (B.old.inclusion x), mem_range_self _⟩ := by
    apply H.injective
    change H (H.symm (B.new.inclusion w)) = H ⟨S.map (B.old.inclusion x), _⟩
    rw [H.apply_symm_apply]
    apply Subtype.ext
    rw [pointActualSectorContractionChart_apply_map]
    exact (B.seam r hr hrold hrnew t ht).symm
  exact congrArg Subtype.val heq

theorem inverse_center (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1) :
    (S.localInverse ha hc hc1 B.new
      (flatLinkSectorDiskApex B.new.angle_pos.le B.new.radius_pos.le)).1 = p := by
  have h := B.inverse_seam ha hc hc1 0 le_rfl B.old.radius_pos.le B.new.radius_pos.le 0
    (Or.inl rfl)
  change (S.localInverse ha hc hc1 B.new
    (flatLinkSectorDiskPoint B.new.angle_pos.le B.new.angle_le_pi 0
      ⟨le_rfl, B.new.radius_pos.le⟩ 0)).1 =
    S.map (B.old.inclusion
      (flatLinkSectorDiskPoint B.old.angle_pos.le B.old.angle_le_pi 0
        ⟨le_rfl, B.old.radius_pos.le⟩ 0)) at h
  rw [flatLinkSectorDiskPoint_zero B.new.angle_pos.le B.new.angle_le_pi
      B.new.radius_pos.le 0,
    flatLinkSectorDiskPoint_zero B.old.angle_pos.le B.old.angle_le_pi
      B.old.radius_pos.le 0] at h
  exact h.trans B.center

theorem center_mem_range (B : PointPairedSectorSurgeryCoordinates S p c) : p ∈ range S.map := by
  rw [← B.center]
  exact mem_range_self _

theorem forward_center (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1) :
    S.localForward ha hc hc1 B.new ⟨p, B.center_mem_range⟩ = 0 := by
  have heq : S.localInverse ha hc hc1 B.new
      (flatLinkSectorDiskApex B.new.angle_pos.le B.new.radius_pos.le) =
        ⟨p, B.center_mem_range⟩ := Subtype.ext (B.inverse_center ha hc hc1)
  rw [← heq, S.localForward_localInverse ha hc hc1 B.new]
  rfl

theorem forward_centered_bounds (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1) (x : range S.map) :
    c * (pointSmoothConformalEDist a y x.1 p).toReal ≤ ‖S.localForward ha hc hc1 B.new x‖ ∧
      ‖S.localForward ha hc hc1 B.new x‖ ≤ (pointSmoothConformalEDist a y x.1 p).toReal := by
  have h := S.localForward_dist_bounds ha hc hc1 B.new x ⟨p, B.center_mem_range⟩
  simpa only [B.forward_center ha hc hc1, dist_zero_right] using h

theorem inverse_small_old_ball (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    {δ : ℝ} (w : flatLinkSectorDisk B.new.angle B.new.radius) (hw : ‖w.1‖ < c * δ) :
    (pointSmoothConformalEDist a y (S.localInverse ha hc hc1 B.new w).1 p).toReal < δ := by
  have h := (S.localInverse_dist_bounds ha hc hc1 B.new w
    (flatLinkSectorDiskApex B.new.angle_pos.le B.new.radius_pos.le)).1
  rw [B.inverse_center ha hc hc1] at h
  change c * (pointSmoothConformalEDist a y (S.localInverse ha hc hc1 B.new w).1 p).toReal ≤
    dist w.1 (0 : ℂ) at h
  rw [dist_zero_right] at h
  nlinarith [h.trans_lt hw]

end PointPairedSectorSurgeryCoordinates

/-- Pair the actual old and new source models at every incident boundary
point. No final atlas, ordered target cover, or new metric is supplied. -/
theorem PointActualAllocatedSector.exists_paired_surgery_coordinates
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {p : ℂ} {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : p ∈ range S.map) (hopen : p ∉ S.openImage) :
    Nonempty (PointPairedSectorSurgeryCoordinates S p c) := by
  classical
  obtain ⟨q, rfl⟩ := hp
  have hqinterior : q.1 ∉ interior (closedEuclideanSector S.beta) :=
    fun hq ↦ hopen ⟨q, hq, rfl⟩
  have hcβ : 0 < c * S.beta := mul_pos hc S.positive
  have hcβπ : c * S.beta ≤ Real.pi :=
    (mul_le_of_le_one_left S.positive.le hc1).trans S.le_pi
  rcases closedEuclideanSector_noninterior_cases S.positive S.le_pi q hqinterior with
    hq0 | ⟨r, hr, top, hqray⟩
  · have hq : q = flatLinkSectorApex S.positive.le := Subtype.ext hq0
    subst q
    refine ⟨{
      old := EuclideanSectorDiskPatch.atApex S.positive S.le_pi (by norm_num : (0 : ℝ) < 1),
      new := EuclideanSectorDiskPatch.atApex hcβ hcβπ (by norm_num : (0 : ℝ) < 1),
      center := rfl,
      old_angle := by simp [PointActualAllocatedSector.apex, EuclideanSectorDiskPatch.atApex],
      new_angle := by simp [PointActualAllocatedSector.apex, EuclideanSectorDiskPatch.atApex],
      seam := ?_
    }⟩
    intro r hr _ _ t _
    change sectorAngularMap c (sectorPolar r (S.beta * t.1)) =
      sectorPolar r ((c * S.beta) * t.1)
    rw [sectorAngularMap_polar hr
      ⟨(neg_neg_of_pos Real.pi_pos).trans_le (mul_nonneg S.positive.le t.2.1),
        (mul_le_of_le_one_right S.positive.le t.2.2).trans S.le_pi⟩]
    congr 1
    ring
  · obtain ⟨Qo, hQoangle, hQor, hQoplace⟩ :=
      EuclideanSectorDiskPatch.exists_atEdge hr S.positive S.le_pi top
    obtain ⟨Qn, hQnangle, hQnr, hQnplace⟩ :=
      EuclideanSectorDiskPatch.exists_atEdge hr hcβ hcβπ top
    have hcenter : S.map (Qo.inclusion
        (flatLinkSectorDiskApex Qo.angle_pos.le Qo.radius_pos.le)) = S.map q := by
      apply congrArg S.map
      apply Subtype.ext
      change Qo.placement 0 = q.1
      rw [hQoplace, hqray]
      simpa only [Complex.ofReal_zero, add_zero] using sectorEdgeChart_real top r S.beta 0
    have hnotapex : S.map q ≠ S.apex := by
      intro he
      have heq : q = flatLinkSectorApex S.positive.le := S.map_injective he
      have hn : ‖q.1‖ = 0 := by rw [heq]; simp [flatLinkSectorApex]
      rw [hqray, sectorPolar_norm hr.le] at hn
      exact hr.ne' hn
    refine ⟨{
      old := Qo, new := Qn, center := hcenter,
      old_angle := by rw [if_neg hnotapex]; exact hQoangle,
      new_angle := by rw [if_neg hnotapex]; exact hQnangle,
      seam := ?_
    }⟩
    intro s hs hsold hsnew t ht
    rw [hQoplace, hQnplace, hQoangle, hQnangle]
    rcases ht with rfl | rfl
    · change sectorAngularMap c (sectorEdgeChart top r S.beta (sectorPolar s (Real.pi * 0))) =
        sectorEdgeChart top r (c * S.beta) (sectorPolar s (Real.pi * 0))
      rw [mul_zero]
      have hs0 : sectorPolar s 0 = (s : ℂ) := by simp [sectorPolar, conePhase]
      rw [hs0]
      exact sectorAngularMap_sectorEdgeChart_real S.positive.le S.le_pi
        (add_nonneg hr.le hs) top
    · change sectorAngularMap c (sectorEdgeChart top r S.beta (sectorPolar s (Real.pi * 1))) =
        sectorEdgeChart top r (c * S.beta) (sectorPolar s (Real.pi * 1))
      rw [mul_one]
      have hsπ : sectorPolar s Real.pi = ((-s : ℝ) : ℂ) := by
        apply Complex.ext <;>
          simp only [sectorPolar_re, sectorPolar_im, Complex.ofReal_re, Complex.ofReal_im,
            Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero]
      rw [hsπ]
      exact sectorAngularMap_sectorEdgeChart_real S.positive.le S.le_pi
        (by linarith [hsnew, hQnr]) top

end RepulsiveCoulomb
