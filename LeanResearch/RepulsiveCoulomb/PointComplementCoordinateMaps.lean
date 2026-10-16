module

public import LeanResearch.RepulsiveCoulomb.PointUnchangedBranchFormulas
public import LeanResearch.RepulsiveCoulomb.ContinuousSubtypeExtension

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual forward/inverse maps for an unchanged
complement piece, extended only by fixed irrelevant outside values. The
identities and continuity are proved on their literal physical domains. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointComplementForward
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius) : ℂ → ℂ :=
  continuousSubtypeExtension (range (pointUnchangedConeSectorMap (β := β) (R := R) C oldlo))
    (fun z ↦ directedSectorPlacement newlo β true
      ((pointUnchangedConeSectorRangeHomeomorph ha y C oldlo hβ hβπ hRC).symm z).1) 0

def pointComplementInverse
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hε : 0 < ε) (hεR : ε ≤ R) : ℂ → ℂ :=
  continuousSubtypeExtension (flatLinkOccupiedDisk ε newlo (newlo + β))
    (fun z ↦ pointUnchangedConeSectorMap C oldlo
      (directedSectorDiskRestriction hβ hβπ hε hεR newlo true z)) p

theorem pointComplementForward_apply_map
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius)
    (w : flatLinkSectorDisk β R) :
    pointComplementForward ha y C oldlo newlo hβ hβπ hRC (pointUnchangedConeSectorMap C oldlo w) =
      directedSectorPlacement newlo β true w.1 := by
  rw [pointComplementForward, continuousSubtypeExtension_eq _ _ _ (mem_range_self w),
    pointUnchangedConeSectorRangeHomeomorph_symm_apply]

theorem pointComplementInverse_apply_target
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hε : 0 < ε) (hεR : ε ≤ R)
    {z : ℂ} (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + β)) :
    pointComplementInverse C oldlo newlo hβ hβπ hε hεR z =
      pointUnchangedConeSectorMap C oldlo
        (directedSectorDiskRestriction hβ hβπ hε hεR newlo true ⟨z, hz⟩) :=
  continuousSubtypeExtension_eq _ _ _ hz

theorem pointComplementInverse_apply_placed
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hε : 0 < ε) (hεR : ε ≤ R)
    (w : flatLinkSectorDisk β R) (hw : ‖w.1‖ ≤ ε) :
    pointComplementInverse C oldlo newlo hβ hβπ hε hεR
      (directedSectorPlacement newlo β true w.1) = pointUnchangedConeSectorMap C oldlo w := by
  have hz : directedSectorPlacement newlo β true w.1 ∈ flatLinkOccupiedDisk ε newlo (newlo + β) := by
    rw [← directedSectorPlacement_disk_range hβ hβπ hε newlo true]
    exact ⟨⟨w.1, w.2.1, hw⟩, rfl⟩
  rw [pointComplementInverse_apply_target C oldlo newlo hβ hβπ hε hεR hz]
  congr 1
  apply Subtype.ext
  exact (directedSectorPlacement newlo β true).symm_apply_apply w.1

theorem pointComplementForward_continuousOn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius) :
    ContinuousOn (pointComplementForward ha y C oldlo newlo hβ hβπ hRC)
      (range (pointUnchangedConeSectorMap (β := β) (R := R) C oldlo)) := by
  apply continuousSubtypeExtension_continuousOn
  exact (directedSectorPlacement newlo β true).continuous.comp
    (continuous_subtype_val.comp (pointUnchangedConeSectorRangeHomeomorph ha y C oldlo hβ hβπ hRC).symm.continuous)

theorem pointComplementInverse_continuousOn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 < R) (hRC : R ≤ C.radius)
    (hε : 0 < ε) (hεR : ε ≤ R) :
    ContinuousOn (pointComplementInverse C oldlo newlo hβ hβπ hε hεR)
      (flatLinkOccupiedDisk ε newlo (newlo + β)) := by
  apply continuousSubtypeExtension_continuousOn
  exact (pointUnchangedConeSectorMap_continuous ha y C oldlo hβ hβπ hR hRC).comp
    (directedSectorDiskRestriction_continuous hβ hβπ hε hεR newlo true)

theorem pointComplement_right_inverse
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius) (hε : 0 < ε) (hεR : ε ≤ R)
    {z : ℂ} (hz : z ∈ flatLinkOccupiedDisk ε newlo (newlo + β)) :
    pointComplementForward ha y C oldlo newlo hβ hβπ hRC
      (pointComplementInverse C oldlo newlo hβ hβπ hε hεR z) = z := by
  rw [pointComplementInverse_apply_target C oldlo newlo hβ hβπ hε hεR hz,
    pointComplementForward_apply_map]
  exact directedSectorDiskRestriction_placed hβ hβπ hε hεR newlo true ⟨z, hz⟩

theorem pointComplement_left_inverse
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hRC : R ≤ C.radius) (hε : 0 < ε) (hεR : ε ≤ R)
    {z : ℂ} (hz : z ∈ range (pointUnchangedConeSectorMap (β := β) (R := R) C oldlo))
    (hF : ‖pointComplementForward ha y C oldlo newlo hβ hβπ hRC z‖ ≤ ε) :
    pointComplementInverse C oldlo newlo hβ hβπ hε hεR
      (pointComplementForward ha y C oldlo newlo hβ hβπ hRC z) = z := by
  obtain ⟨w, rfl⟩ := hz
  rw [pointComplementForward_apply_map] at hF ⊢
  rw [directedSectorPlacement_norm] at hF
  exact pointComplementInverse_apply_placed C oldlo newlo hβ hβπ hε hεR w hF

theorem pointComplementForward_center
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 ≤ R) (hRC : R ≤ C.radius) :
    pointComplementForward ha y C oldlo newlo hβ hβπ hRC p = 0 := by
  let w := flatLinkSectorDiskApex hβ.le hR
  have hg : pointUnchangedConeSectorMap C oldlo w = p := pointUnchangedConeSectorMap_center C oldlo hβ.le hR
  have h := pointComplementForward_apply_map ha y C oldlo newlo hβ hβπ hRC w
  rw [hg] at h
  exact h.trans (directedSectorPlacement_zero newlo β true)

theorem pointComplementInverse_center
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) (oldlo newlo : ℝ) {β R ε : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hR : 0 ≤ R) (hε : 0 < ε) (hεR : ε ≤ R) :
    pointComplementInverse C oldlo newlo hβ hβπ hε hεR 0 = p := by
  let w := flatLinkSectorDiskApex hβ.le hR
  have hw : ‖w.1‖ ≤ ε := by change ‖(0 : ℂ)‖ ≤ ε; simpa only [norm_zero] using hε.le
  have h := pointComplementInverse_apply_placed C oldlo newlo hβ hβπ hε hεR w hw
  have hg : pointUnchangedConeSectorMap C oldlo w = p :=
    pointUnchangedConeSectorMap_center C oldlo hβ.le hR
  have hz : directedSectorPlacement newlo β true w.1 = 0 :=
    directedSectorPlacement_zero newlo β true
  rw [hz,hg] at h
  exact h

end RepulsiveCoulomb
