import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskTwoAnchorUniqueness
import LeanResearch.RepulsiveCoulomb.MetricSupportedFlatPatchCompatibility

/-! ISOLATED SOURCE-ONLY DRAFT, 2026-10-03. No compiler invocation.

A genuine relative patch at a source supporting-line point. An actual
Euclidean rigid coordinate sends the supporting halfplane to Im >= 0. The
whole target halfdisk is aligned using an actual two-sided old-boundary
arclength interval. Only two points of that interval must lie in the old
rectangle: the center and one other point. In particular, the rectangle may
end at the center along the compact edge. There is no interior-H premise,
full-disk premise, patch-existence premise, or new-map agreement premise.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- The actual closed supporting halfplane, in a specified rigid coordinate. -/
def rigidUpperHalfplane (E : ℂ ≃ᵢ ℂ) : Set ℂ := {z | 0 ≤ (E z).im}

/-- Restrict a global Euclidean rigid coordinate to its whole relative ball. -/
def rigidUpperHalfDiskEquiv (E : ℂ ≃ᵢ ℂ) {q : ℂ} (hq : E q = 0) (R : ℝ) :
    supportedFlatPatch (rigidUpperHalfplane E) q R ≃ᵢ flatUpperDisk R := by
  have hnorm (z : ℂ) : ‖E z‖ = dist z q := by
    rw [← dist_zero_right, ← hq, E.dist_eq]
  let F : supportedFlatPatch (rigidUpperHalfplane E) q R → flatUpperDisk R :=
    fun z ↦ ⟨E z.1, by rw [hnorm]; exact z.2.1, z.2.2⟩
  let G : flatUpperDisk R → supportedFlatPatch (rigidUpperHalfplane E) q R :=
    fun z ↦ ⟨E.symm z.1, by
      constructor
      · change dist (E.symm z.1) q < R
        rw [← hnorm, E.apply_symm_apply]
        exact z.2.1
      · change 0 ≤ (E (E.symm z.1)).im
        rw [E.apply_symm_apply]
        exact z.2.2⟩
  refine { toFun := F, invFun := G, left_inv := ?_, right_inv := ?_, isometry_toFun := ?_ }
  · intro z
    apply Subtype.ext
    exact E.symm_apply_apply z.1
  · intro z
    apply Subtype.ext
    exact E.apply_symm_apply z.1
  · apply Isometry.of_dist_eq
    intro z w
    exact E.dist_eq z.1 w.1

/-- Construct and align the actual whole relative halfdisk patch. The boundary
interval is geometric input, not a patch certificate. It may extend past the
old compact edge, while the two alignment anchors themselves are old points.
The second anchor parameter may have either sign. -/
theorem exists_relative_halfDisk_patch_extension {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (f : K → Y) (hf : Isometry f) (q q₁ : K)
    (E : ℂ ≃ᵢ ℂ) (hq : E q.1 = 0)
    (C : MetricFlatHalfDiskChart Y (f q))
    {L : ℝ} (hL : 0 < L) (hLR : L < C.radius)
    (ρ : Icc (-L) L → Y) (hρ : Isometry ρ)
    (hρzero : ρ (complexSymmetricIntervalZero hL) = f q)
    (b : Icc (-L) L) (hb : b.1 ≠ 0)
    (hq₁ : E q₁.1 = (b.1 : ℂ)) (hρb : ρ b = f q₁) :
    ∃ e : supportedFlatPatch (rigidUpperHalfplane E) q.1 C.radius ≃ᵢ
        ball (f q) C.radius,
      ∀ x : K,
        ∀ hx : x.1 ∈ supportedFlatPatch (rigidUpperHalfplane E) q.1 C.radius,
          (e ⟨x.1, hx⟩).1 = f x := by
  obtain ⟨D, hD0, hDb⟩ := C.exists_aligned_to_short_interval hL hLR ρ hρ hρzero
  let A := rigidUpperHalfDiskEquiv E hq C.radius
  let e := A.trans D
  have hqmem : q.1 ∈ supportedFlatPatch (rigidUpperHalfplane E) q.1 C.radius := by
    constructor
    · exact mem_ball_self C.radius_pos
    · change 0 ≤ (E q.1).im
      rw [hq]
      simp
  have hbmem : (b.1 : ℂ) ∈ flatUpperDisk C.radius := (halfDiskIntervalReal hLR b).2
  have h0mem : (0 : ℂ) ∈ flatUpperDisk C.radius := (flatUpperDiskZero C.radius_pos).2
  have hq₁mem : q₁.1 ∈ supportedFlatPatch (rigidUpperHalfplane E) q.1 C.radius := by
    constructor
    · change dist q₁.1 q.1 < C.radius
      rw [← E.dist_eq, hq₁, hq, dist_zero_right]
      exact hbmem.1
    · change 0 ≤ (E q₁.1).im
      rw [hq₁]
      simp
  have heq : e ⟨q.1, hqmem⟩ = D ⟨0, h0mem⟩ := by
    apply congrArg D
    apply Subtype.ext
    exact hq
  have heq₁ : e ⟨q₁.1, hq₁mem⟩ = D ⟨(b.1 : ℂ), hbmem⟩ := by
    apply congrArg D
    apply Subtype.ext
    exact hq₁
  have heqval : (e ⟨q.1, hqmem⟩).1 = f q := by
    rw [heq]
    exact hD0
  have heq₁val : (e ⟨q₁.1, hq₁mem⟩).1 = f q₁ := by
    rw [heq₁]
    exact (hDb b).trans hρb
  refine ⟨e, ?_⟩
  intro x hx
  have hxball : f x ∈ ball (f q) C.radius := by
    change dist (f x) (f q) < C.radius
    rw [hf.dist_eq]
    exact hx.1
  have hzero : dist (e ⟨x.1, hx⟩) (D ⟨0, h0mem⟩) =
      dist (⟨f x, hxball⟩ : ball (f q) C.radius) (D ⟨0, h0mem⟩) := by
    rw [← heq, e.dist_eq]
    change dist x.1 q.1 = dist (f x) (e ⟨q.1, hqmem⟩).1
    rw [heqval, hf.dist_eq]
    rfl
  have hsecond : dist (e ⟨x.1, hx⟩) (D ⟨(b.1 : ℂ), hbmem⟩) =
      dist (⟨f x, hxball⟩ : ball (f q) C.radius) (D ⟨(b.1 : ℂ), hbmem⟩) := by
    rw [← heq₁, e.dist_eq]
    change dist x.1 q₁.1 = dist (f x) (e ⟨q₁.1, hq₁mem⟩).1
    rw [heq₁val, hf.dist_eq]
    rfl
  exact congrArg Subtype.val (metricHalfDisk_two_anchor_unique D
    (Ne.symm hb) h0mem hbmem hzero hsecond)

end RepulsiveCoulomb
