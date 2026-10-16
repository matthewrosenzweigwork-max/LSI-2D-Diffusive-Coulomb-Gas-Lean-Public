module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorContractionChart

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Genuine local coordinates on a physical closed
sector, centered using an explicitly described Euclidean patch in its actual
contracted target. The forward map, inverse map, sharp pair bounds and both
inverse identities are constructed together. No ambient open chart is an
input; these are individual pieces for the finite paste. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

structure EuclideanSectorDiskPatch (β : ℝ) where
  angle : ℝ
  angle_pos : 0 < angle
  angle_le_pi : angle ≤ Real.pi
  radius : ℝ
  radius_pos : 0 < radius
  placement : ℂ ≃ᵢ ℂ
  membership : ∀ w : ℂ, ‖w‖ ≤ radius →
    (placement w ∈ closedEuclideanSector β ↔ w ∈ closedEuclideanSector angle)

namespace EuclideanSectorDiskPatch
variable {β : ℝ}

def inclusion (Q : EuclideanSectorDiskPatch β) :
    flatLinkSectorDisk Q.angle Q.radius → closedEuclideanSector β := fun w ↦
  ⟨Q.placement w.1, (Q.membership w.1 w.2.2).mpr w.2.1⟩

theorem inclusion_isometry (Q : EuclideanSectorDiskPatch β) : Isometry Q.inclusion := by
  apply Isometry.of_dist_eq
  intro x z
  exact Q.placement.dist_eq x.1 z.1

theorem inclusion_range (Q : EuclideanSectorDiskPatch β) :
    range Q.inclusion = {q : closedEuclideanSector β | dist q.1 (Q.placement 0) ≤ Q.radius} := by
  ext q
  constructor
  · rintro ⟨w, rfl⟩
    change dist (Q.placement w.1) (Q.placement 0) ≤ Q.radius
    rw [Q.placement.dist_eq, dist_zero_right]
    exact w.2.2
  · intro hq
    let w := Q.placement.symm q.1
    have hwn : ‖w‖ ≤ Q.radius := by
      rw [← dist_zero_right, ← Q.placement.dist_eq, Q.placement.apply_symm_apply]
      exact hq
    have hwS : w ∈ closedEuclideanSector Q.angle := (Q.membership w hwn).mp (by
      simpa only [w, Q.placement.apply_symm_apply] using q.2)
    exact ⟨⟨w, hwS, hwn⟩, Subtype.ext (Q.placement.apply_symm_apply q.1)⟩

theorem inclusion_mem_interior (Q : EuclideanSectorDiskPatch β)
    (w : flatLinkSectorDisk Q.angle Q.radius)
    (hw : w.1 ∈ interior (closedEuclideanSector Q.angle)) (hwR : ‖w.1‖ < Q.radius) :
    (Q.inclusion w).1 ∈ interior (closedEuclideanSector β) := by
  let V : Set ℂ := interior (closedEuclideanSector Q.angle) ∩ Metric.ball 0 Q.radius
  have hV : IsOpen V := isOpen_interior.inter Metric.isOpen_ball
  let U : Set ℂ := Q.placement.symm ⁻¹' V
  have hU : IsOpen U := hV.preimage Q.placement.symm.continuous
  have hUK : U ⊆ closedEuclideanSector β := by
    intro z hz
    have hnorm : ‖Q.placement.symm z‖ ≤ Q.radius := by
      have hh : dist (Q.placement.symm z) 0 < Q.radius := hz.2
      simpa only [dist_zero_right] using hh.le
    have hmem := (Q.membership (Q.placement.symm z) hnorm).mpr (interior_subset hz.1)
    simpa only [Q.placement.apply_symm_apply] using hmem
  have hwU : (Q.inclusion w).1 ∈ U := by
    change Q.placement.symm (Q.placement w.1) ∈ interior (closedEuclideanSector Q.angle) ∩
      Metric.ball 0 Q.radius
    rw [Q.placement.symm_apply_apply]
    exact ⟨hw, by simpa only [Metric.mem_ball, dist_zero_right] using hwR⟩
  exact interior_mono hUK (by simpa only [hU.interior_eq] using hwU)

/-- The own-apex target is the contracted sector itself. -/
def atApex {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) {R : ℝ} (hR : 0 < R) :
    EuclideanSectorDiskPatch β where
  angle := β
  angle_pos := hβ
  angle_le_pi := hβπ
  radius := R
  radius_pos := hR
  placement := IsometryEquiv.refl ℂ
  membership := fun _ _ ↦ Iff.rfl

/-- The nonapex target is the explicitly centered halfdisk in the actual
contracted sector; the radius and membership equality are constructed. -/
theorem exists_atEdge {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (top : Bool) : ∃ Q : EuclideanSectorDiskPatch β,
      Q.angle = Real.pi ∧ Q.radius < r ∧ Q.placement = sectorEdgeChart top r β := by
  obtain ⟨R, hR, hRr, hmem⟩ := exists_sectorEdge_centeredHalfDisk hr hβ hβπ top
  let Q : EuclideanSectorDiskPatch β := {
    angle := Real.pi, angle_pos := Real.pi_pos, angle_le_pi := le_rfl,
    radius := R, radius_pos := hR, placement := sectorEdgeChart top r β,
    membership := fun w hw ↦ by
      dsimp only [sectorEdgeChart]
      rw [hmem w hw]
      simp only [closedEuclideanSector, mem_setOf_eq, Complex.arg_nonneg_iff,
        Complex.arg_le_pi, and_true]
  }
  exact ⟨Q, rfl, hRr, rfl⟩

end EuclideanSectorDiskPatch

namespace PointActualAllocatedSector
variable {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)

def localForward (Q : EuclideanSectorDiskPatch (c * S.beta)) : range S.map → ℂ :=
  fun x ↦ Q.placement.symm (pointActualSectorContractionChart ha S hc hc1 x)

def localInverse (Q : EuclideanSectorDiskPatch (c * S.beta)) :
    flatLinkSectorDisk Q.angle Q.radius → range S.map :=
  (pointActualSectorContractionChart ha S hc hc1).symm ∘ Q.inclusion

theorem localForward_continuous (Q : EuclideanSectorDiskPatch (c * S.beta)) :
    Continuous (S.localForward ha hc hc1 Q) :=
  Q.placement.symm.continuous.comp (continuous_subtype_val.comp
    (pointActualSectorContractionChart ha S hc hc1).continuous)

theorem localInverse_continuous (Q : EuclideanSectorDiskPatch (c * S.beta)) :
    Continuous (S.localInverse ha hc hc1 Q) :=
  (pointActualSectorContractionChart ha S hc hc1).symm.continuous.comp Q.inclusion_isometry.continuous

theorem localForward_dist_bounds (Q : EuclideanSectorDiskPatch (c * S.beta))
    (x z : range S.map) :
    c * (pointSmoothConformalEDist a y x.1 z.1).toReal ≤
      dist (S.localForward ha hc hc1 Q x) (S.localForward ha hc hc1 Q z) ∧
      dist (S.localForward ha hc hc1 Q x) (S.localForward ha hc hc1 Q z) ≤
        (pointSmoothConformalEDist a y x.1 z.1).toReal := by
  simp only [localForward, Q.placement.symm.dist_eq]
  exact pointActualSectorContractionChart_dist_bounds ha S hc hc1 x z

@[simp] theorem localForward_localInverse (Q : EuclideanSectorDiskPatch (c * S.beta))
    (w : flatLinkSectorDisk Q.angle Q.radius) :
    S.localForward ha hc hc1 Q (S.localInverse ha hc hc1 Q w) = w.1 := by
  change Q.placement.symm
    ((pointActualSectorContractionChart ha S hc hc1)
      ((pointActualSectorContractionChart ha S hc hc1).symm (Q.inclusion w))) = w.1
  rw [(pointActualSectorContractionChart ha S hc hc1).apply_symm_apply]
  exact Q.placement.symm_apply_apply w.1

theorem localForward_mem_sector (Q : EuclideanSectorDiskPatch (c * S.beta))
    (x : range S.map) (hx : ‖S.localForward ha hc hc1 Q x‖ ≤ Q.radius) :
    S.localForward ha hc hc1 Q x ∈ closedEuclideanSector Q.angle := by
  apply (Q.membership _ hx).mp
  change Q.placement (Q.placement.symm
    (pointActualSectorContractionChart ha S hc hc1 x)) ∈ closedEuclideanSector (c * S.beta)
  rw [Q.placement.apply_symm_apply]
  exact (pointActualSectorContractionChart ha S hc hc1 x).2

theorem localInverse_localForward (Q : EuclideanSectorDiskPatch (c * S.beta))
    (x : range S.map) (hx : ‖S.localForward ha hc hc1 Q x‖ ≤ Q.radius) :
    S.localInverse ha hc hc1 Q
      ⟨S.localForward ha hc hc1 Q x, S.localForward_mem_sector ha hc hc1 Q x hx, hx⟩ = x := by
  apply (pointActualSectorContractionChart ha S hc hc1).injective
  change (pointActualSectorContractionChart ha S hc hc1)
      ((pointActualSectorContractionChart ha S hc hc1).symm (Q.inclusion _)) = _
  rw [(pointActualSectorContractionChart ha S hc hc1).apply_symm_apply]
  apply Subtype.ext
  exact Q.placement.apply_symm_apply _

theorem localInverse_dist_bounds (Q : EuclideanSectorDiskPatch (c * S.beta))
    (x z : flatLinkSectorDisk Q.angle Q.radius) :
    c * (pointSmoothConformalEDist a y (S.localInverse ha hc hc1 Q x).1
      (S.localInverse ha hc hc1 Q z).1).toReal ≤ dist x z ∧
      dist x z ≤ (pointSmoothConformalEDist a y (S.localInverse ha hc hc1 Q x).1
        (S.localInverse ha hc hc1 Q z).1).toReal := by
  have h := S.localForward_dist_bounds ha hc hc1 Q
    (S.localInverse ha hc hc1 Q x) (S.localInverse ha hc hc1 Q z)
  simpa only [S.localForward_localInverse ha hc hc1 Q, Subtype.dist_eq] using h

end PointActualAllocatedSector
end RepulsiveCoulomb
