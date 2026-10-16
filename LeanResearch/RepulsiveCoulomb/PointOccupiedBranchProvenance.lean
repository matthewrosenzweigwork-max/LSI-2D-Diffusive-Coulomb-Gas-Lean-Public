module

public import LeanResearch.RepulsiveCoulomb.PointOccupiedRefinedAngularBranch

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Preserve the literal occupied branch formula
through existential assembly, so later rigid-overlap proofs can compare the
same global sector contraction instead of merely bi-Lipschitz constants. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb
namespace PointPairedSectorSurgeryCoordinates
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ} {c : ℝ}

theorem exists_ownedRefinedAngularBranch_with_formula (B : PointPairedSectorSurgeryCoordinates S p c)
    (ha : ∀ j, 0 ≤ a j) (hc : 0 < c) (hc1 : c ≤ 1)
    (C : PointFlatLinkConeDisk a y p) {R ε : ℝ}
    (hR : 0 < R) (hRold : R ≤ B.old.radius) (hRnew : R ≤ B.new.radius)
    (hRC : R ≤ C.radius) (hε : 0 < ε) (hεcR : ε ≤ c * R)
    {lo : ℝ} {forward : Bool} (hpolar : B.sourcePatch.PolarAt C hRold lo forward)
    (origin : ℝ)
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (i : ι) (v : Fin (Q.count (owner i)))
    (holdlo : u (owner i).castSucc = normalizedIncidentLower origin lo)
    (holdhi : u (owner i).succ = normalizedIncidentLower origin lo +
      B.old.angle / (coalescedPointExponent a y p / 2 + 1))
    (hwidth : width (owner i) = B.new.angle) :
    ∃ F : PointRefinedAngularBranch (C.rotate (-origin)) R ε Q width ⟨owner i, v⟩,
      F.forward = B.occupiedForward ha hc hc1
        (linkCumulativeWidth (finiteLinkWidthSequence width) (owner i).1) forward ∧
      (∀ z ∈ pointConeOpenBall (C.rotate (-origin)) R ∩
          pointRefinedSourceSet (C.rotate (-origin)) R Q ⟨owner i, v⟩,
        ∀ w ∈ pointConeOpenBall (C.rotate (-origin)) R ∩
          pointRefinedSourceSet (C.rotate (-origin)) R Q ⟨owner i, v⟩,
        c * (pointSmoothConformalEDist a y z w).toReal ≤ dist (F.forward z) (F.forward w) ∧
          dist (F.forward z) (F.forward w) ≤ (pointSmoothConformalEDist a y z w).toReal) ∧
      (∀ z ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width ⟨owner i, v⟩,
        ∀ w ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width ⟨owner i, v⟩,
        c * (pointSmoothConformalEDist a y (F.inverse z) (F.inverse w)).toReal ≤ dist z w ∧
          dist z w ≤ (pointSmoothConformalEDist a y (F.inverse z) (F.inverse w)).toReal) := by
  classical
  let D := C.rotate (-origin)
  let newlo := linkCumulativeWidth (finiteLinkWidthSequence width) (owner i).1
  have hεR : ε ≤ R := hεcR.trans (mul_le_of_le_one_left hR.le hc1)
  have hεnew : ε ≤ B.new.radius := hεR.trans hRnew
  have howned : owner i ∈ range owner := mem_range_self i
  have hcount : Q.count (owner i) = 1 := Q.occupied_whole (owner i) howned
  have hv0 : v.1 = 0 := by have hv := v.2; omega
  have hvfirst : v.castSucc = (0 : Fin (Q.count (owner i) + 1)) := Fin.ext hv0
  have hvlast : v.succ = Fin.last (Q.count (owner i)) := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have hsource {z : ℂ} (hz : z ∈ pointConeOpenBall D R ∩
      pointRefinedSourceSet D R Q ⟨owner i, v⟩) : z ∈ range S.map := by
    have hd := (mem_pointConeOpenBall_iff D (show R ≤ D.radius from hRC) z).mp hz.1
    apply (B.sourcePatch.rotated_normalized_range_iff ha C hR hRold hRC hpolar origin hd.le).mpr
    simpa only [pointRefinedSourceSet, mem_setOf_eq, hvfirst, hvlast, Q.first, Q.last,
      holdlo, holdhi, D, sourcePatch] using hz.2
  have htarget {z : ℂ} (hz : z ∈ pointRefinedTargetSet ε Q width ⟨owner i, v⟩) :
      z ∈ flatLinkOccupiedDisk ε newlo (newlo + B.new.angle) := by
    simpa only [pointRefinedTargetSet, refinedIncidentTargetNode, if_pos howned,
      Fin.val_castSucc, Fin.val_succ, hv0, Nat.zero_add, Nat.cast_zero, Nat.cast_one,
      zero_mul, one_mul, add_zero, hwidth] using hz
  let F := B.ownedRefinedAngularBranch ha hc hc1 C hR hRold hRnew hRC hε hεcR
    hpolar origin Q width i v holdlo holdhi hwidth
  refine ⟨F, rfl, ?_, ?_⟩
  · intro z hz w hw
    change c * (pointSmoothConformalEDist a y z w).toReal ≤
        dist (B.occupiedForward ha hc hc1 newlo forward z)
          (B.occupiedForward ha hc hc1 newlo forward w) ∧ _
    exact B.occupiedForward_dist_bounds ha hc hc1 newlo forward (hsource hz) (hsource hw)
  · intro z hz w hw
    change c * (pointSmoothConformalEDist a y
      (B.occupiedInverse ha hc hc1 hε hεnew newlo forward z)
      (B.occupiedInverse ha hc hc1 hε hεnew newlo forward w)).toReal ≤ dist z w ∧ _
    exact B.occupiedInverse_dist_bounds ha hc hc1 hε hεnew newlo forward
      (htarget hz.2) (htarget hw.2)


end PointPairedSectorSurgeryCoordinates
end RepulsiveCoulomb
