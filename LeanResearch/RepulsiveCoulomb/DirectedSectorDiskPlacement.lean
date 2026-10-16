module

public import LeanResearch.RepulsiveCoulomb.DirectedSectorPlacement

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The ordered target wedge is exactly the image
of the literal new sector disk under its explicit Euclidean placement. Both
directions and boundary endpoints are included, with exact radial norm. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem directedSectorPlacement_norm (lo width : ℝ) (forward : Bool) (z : ℂ) :
    ‖directedSectorPlacement lo width forward z‖ = ‖z‖ := by
  have h := (directedSectorPlacement lo width forward).dist_eq z 0
  simpa only [directedSectorPlacement_zero, dist_zero_right] using h

theorem directedSectorPlacement_symm_norm (lo width : ℝ) (forward : Bool) (z : ℂ) :
    ‖(directedSectorPlacement lo width forward).symm z‖ = ‖z‖ := by
  have h := directedSectorPlacement_norm lo width forward
    ((directedSectorPlacement lo width forward).symm z)
  rw [(directedSectorPlacement lo width forward).apply_symm_apply] at h
  exact h.symm

theorem directedSectorPlacement_disk_range {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 < R) (lo : ℝ) (forward : Bool) :
    range (fun x : flatLinkSectorDisk β R ↦ directedSectorPlacement lo β forward x.1) =
      flatLinkOccupiedDisk R lo (lo + β) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨s, t, hst⟩ := flatLinkSectorDisk_representation hβ hβπ hR le_rfl x x.2.2
    rw [hst]
    change directedSectorPlacement lo β forward (sectorPolar (R * s.1) (β * t.1)) ∈
      flatLinkOccupiedDisk R lo (lo + β)
    rw [directedSectorPlacement_polar_unitInterval]
    have ht := flatLinkOrientedAngle_mem forward hβ.le t
    exact ⟨R * s.1, ⟨mul_nonneg hR.le s.2.1, mul_le_of_le_one_right hR.le s.2.2⟩,
      lo + flatLinkOrientedAngle forward β t,
      ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  · rintro ⟨r, hr, θ, hθ, he⟩
    obtain ⟨t, ht⟩ := flatLinkOrientedAngle_surjective forward hβ
      (show θ - lo ∈ Icc (0 : ℝ) β from ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    refine ⟨flatLinkSectorDiskPoint hβ.le hβπ r hr t, ?_⟩
    change directedSectorPlacement lo β forward (sectorPolar r (β * t.1)) = z
    rw [directedSectorPlacement_polar_unitInterval]
    have hθeq : lo + flatLinkOrientedAngle forward β t = θ := by linarith [ht]
    rw [hθeq]
    exact he.symm

/-- An actual target wedge point has exactly the inverse sector membership
needed to evaluate the physical inverse branch. -/
theorem directedSectorPlacement_mem_disk_iff {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 < R) (lo : ℝ) (forward : Bool) (z : ℂ) :
    z ∈ flatLinkOccupiedDisk R lo (lo + β) ↔
      (directedSectorPlacement lo β forward).symm z ∈ flatLinkSectorDisk β R := by
  rw [← directedSectorPlacement_disk_range hβ hβπ hR lo forward]
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [(directedSectorPlacement lo β forward).symm_apply_apply] using x.2
  · intro hz
    exact ⟨⟨(directedSectorPlacement lo β forward).symm z, hz⟩,
      (directedSectorPlacement lo β forward).apply_symm_apply z⟩

end RepulsiveCoulomb
