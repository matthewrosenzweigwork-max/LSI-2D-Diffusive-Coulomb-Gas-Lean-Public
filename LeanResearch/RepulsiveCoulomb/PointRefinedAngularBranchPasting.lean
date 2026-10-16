module

public import LeanResearch.RepulsiveCoulomb.RefinedIncidentSeamCorrespondence
public import LeanResearch.RepulsiveCoulomb.PointConeBallClosedPieceCover
public import LeanResearch.RepulsiveCoulomb.FiniteClosedPieceOpenChart

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Paste the physical branches over the actually
constructed refined angular covers. Forward and inverse overlap agreement
are derived from actual endpoint formulas and the proved cyclic node
correspondence, not supplied as seam-compatibility fields. This constructor
is to be instantiated by the occupied and unchanged branch producers. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace RepulsiveCoulomb

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}

def pointRefinedSourceSet (C : PointFlatLinkConeDisk a y p) (R : ℝ)
    (Q : FiniteLinkComplementRefinement u owner k)
    (x : Σ j : Fin N, Fin (Q.count j)) : Set ℂ :=
  {z | C.chart z ∈ flatLinkOccupiedDisk R (Q.node x.1 x.2.castSucc) (Q.node x.1 x.2.succ)}

def pointRefinedTargetSet (r : ℝ) (Q : FiniteLinkComplementRefinement u owner k)
    (width : Fin N → ℝ) (x : Σ j : Fin N, Fin (Q.count j)) : Set ℂ :=
  flatLinkOccupiedDisk r (refinedIncidentTargetNode Q width x.1 x.2.castSucc)
    (refinedIncidentTargetNode Q width x.1 x.2.succ)

/-- Local laws of one actual physical branch. The source and target angular
pieces are fixed by the constructed partition, not chosen by this record. -/
structure PointRefinedAngularBranch (C : PointFlatLinkConeDisk a y p) (R r : ℝ)
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (x : Σ j : Fin N, Fin (Q.count j)) where
  forward : ℂ → ℂ
  inverse : ℂ → ℂ
  forward_continuous : ContinuousOn forward (pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x)
  inverse_continuous : ContinuousOn inverse (ball 0 r ∩ pointRefinedTargetSet r Q width x)
  forward_target : ∀ z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
    forward z ∈ ball 0 r → forward z ∈ pointRefinedTargetSet r Q width x
  inverse_source : ∀ z ∈ ball 0 r ∩ pointRefinedTargetSet r Q width x,
    inverse z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x
  left_inv : ∀ z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
    forward z ∈ ball 0 r → inverse (forward z) = z
  right_inv : ∀ z ∈ ball 0 r ∩ pointRefinedTargetSet r Q width x, forward (inverse z) = z
  forward_center : forward p = 0
  inverse_center : inverse 0 = p
  forward_endpoint : ∀ z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
    ∀ s : ℝ, 0 ≤ s → ∀ top : Bool,
      C.chart z = sectorPolar s (refinedIncidentSourceEndpoint Q x top) →
        forward z = sectorPolar s (refinedIncidentTargetEndpoint Q width x top)
  inverse_endpoint : ∀ z ∈ ball 0 r ∩ pointRefinedTargetSet r Q width x,
    ∀ s : ℝ, 0 ≤ s → ∀ top : Bool,
      z = sectorPolar s (refinedIncidentTargetEndpoint Q width x top) →
        C.chart (inverse z) = sectorPolar s (refinedIncidentSourceEndpoint Q x top)

/-- Construct an actual open chart from the physical branch laws on the
proved refined cover. Both seam agreements follow from endpoint geometry. -/
theorem exists_openChart_of_refined_angular_branches
    (C : PointFlatLinkConeDisk a y p) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hN : 0 < N) (hu : StrictMono u) (hu0 : u 0 = 0) (huT : u (Fin.last N) = 2 * Real.pi)
    (Q : FiniteLinkComplementRefinement u owner k) (hk : 0 < k)
    (width : Fin N → ℝ) (hw : ∀ j, 0 < width j)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc))
    (htotal : (∑ j, width j) = 2 * Real.pi)
    (B : ∀ x : (Σ j : Fin N, Fin (Q.count j)), PointRefinedAngularBranch C R r Q width x) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.source ⊆ pointConeOpenBall C R ∧ e.target = ball 0 r ∧
      (∀ i z, z ∈ e.source → z ∈ pointRefinedSourceSet C R Q i → e z = (B i).forward z) ∧
      (∀ i z, z ∈ ball 0 r → z ∈ pointRefinedTargetSet r Q width i → e.symm z = (B i).inverse z) := by
  classical
  let U := pointConeOpenBall C R
  let V : Set ℂ := ball 0 r
  let S := pointRefinedSourceSet C R Q
  let T := pointRefinedTargetSet r Q width
  have hSclosed : ∀ i, IsClosed {z : U | z.1 ∈ S i} := fun i ↦
    pointConeBallAngularPiece_isClosed C R (Q.node i.1 i.2.castSucc) (Q.node i.1 i.2.succ)
  have hTclosed : ∀ i, IsClosed {z : V | z.1 ∈ T i} := fun i ↦
    (flatLinkOccupiedDisk_isClosed r
      (refinedIncidentTargetNode Q width i.1 i.2.castSucc)
      (refinedIncidentTargetNode Q width i.1 i.2.succ)).preimage continuous_subtype_val
  have hScover : ∀ z ∈ U, ∃ i, z ∈ S i := by
    intro z hz
    have hn : ‖C.chart z‖ ≤ R := by
      have hh : dist (C.chart z) 0 < R := hz.2
      simpa only [dist_zero_right] using hh.le
    exact finiteLinkComplementRefinement_whole_source_cover hN hu0 huT Q R hn
  have hTcover : ∀ z ∈ V, ∃ i, z ∈ T i := by
    intro z hz
    have hn : ‖z‖ ≤ r := by
      have hh : dist z 0 < r := hz
      simpa only [dist_zero_right] using hh.le
    exact refinedIncidentTargetWedges_cover hN Q width hcomp htotal r hn
  have hfseam : ∀ i j z, z ∈ U → z ∈ S i → z ∈ S j → (B i).forward z = (B j).forward z := by
    intro i j z hz hi hj
    by_cases hij : i = j
    · subst j; rfl
    by_cases hz0 : C.chart z = 0
    · have hzp : z = p := C.chart.injOn hz.1 C.center_mem (hz0.trans C.center.symm)
      rw [hzp, (B i).forward_center, (B j).forward_center]
    · obtain ⟨s, hs, b, d, hzi, hzj⟩ :=
        refinedIncident_source_overlap_endpoints Q hu hu0 huT i j hij hz0 hi hj
      rw [(B i).forward_endpoint z ⟨hz, hi⟩ s hs.le b hzi,
        (B j).forward_endpoint z ⟨hz, hj⟩ s hs.le d hzj]
      exact (refinedIncident_boundary_seam_iff Q hu hu0 huT hk width hw hcomp htotal
        hs.le hs.le i j b d).mp (hzi.symm.trans hzj)
  have hgseam : ∀ i j z, z ∈ V → z ∈ T i → z ∈ T j → (B i).inverse z = (B j).inverse z := by
    intro i j z hz hi hj
    by_cases hij : i = j
    · subst j; rfl
    by_cases hz0 : z = 0
    · rw [hz0, (B i).inverse_center, (B j).inverse_center]
    · obtain ⟨s, hs, b, d, hzi, hzj⟩ :=
        refinedIncident_target_overlap_endpoints Q hk width hw hcomp htotal i j hij hz0 hi hj
      apply C.chart.injOn ((B i).inverse_source z ⟨hz, hi⟩).1.1
        ((B j).inverse_source z ⟨hz, hj⟩).1.1
      rw [(B i).inverse_endpoint z ⟨hz, hi⟩ s hs.le b hzi,
        (B j).inverse_endpoint z ⟨hz, hj⟩ s hs.le d hzj]
      exact (refinedIncident_boundary_seam_iff Q hu hu0 huT hk width hw hcomp htotal
        hs.le hs.le i j b d).mpr (hzi.symm.trans hzj)
  let e := openPartialHomeomorphOfFiniteClosedPiecesWithin U V (pointConeOpenBall_isOpen C R)
    isOpen_ball S T hSclosed hTclosed hScover hTcover
    (fun i ↦ (B i).forward) (fun i ↦ (B i).inverse) p 0
    (fun i ↦ (B i).forward_continuous) (fun i ↦ (B i).inverse_continuous)
    (fun i z hz hi hV ↦ (B i).forward_target z ⟨hz, hi⟩ hV)
    (fun i z hz hi ↦ (B i).inverse_source z ⟨hz, hi⟩)
    (fun i z hz hi hV ↦ (B i).left_inv z ⟨hz, hi⟩ hV)
    (fun i z hz hi ↦ (B i).right_inv z ⟨hz, hi⟩) hfseam hgseam
  have hpU : p ∈ U := pointConeOpenBall_center C hR
  have hep : e p = 0 := by
    obtain ⟨i, hi⟩ := hScover p hpU
    exact (finiteCoverGlueWithin_eq U S hScover (fun i ↦ (B i).forward) 0 hfseam hpU hi).trans
      (B i).forward_center
  refine ⟨e, ⟨hpU, ?_⟩, hep, inter_subset_left, rfl, ?_, ?_⟩
  · change e p ∈ ball 0 r
    rw [hep]
    exact mem_ball_self hr
  · intro i z hz hi
    exact finiteCoverGlueWithin_eq U S hScover (fun i ↦ (B i).forward) 0 hfseam hz.1 hi
  · intro i z hz hi
    exact finiteCoverGlueWithin_eq V T hTcover (fun i ↦ (B i).inverse) p hgseam hz hi

end RepulsiveCoulomb
