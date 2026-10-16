module

public import LeanResearch.RepulsiveCoulomb.FiniteRefinedWedgeOverlap
public import LeanResearch.RepulsiveCoulomb.PointConstructedRefinedAngles

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Instantiate two-sided cyclic seam compatibility
and distinct-cell overlap classification on the actual complement refinement.
The target nodes are exactly refinedIncidentTargetNode; no independent target
node choice or desired seam-compatibility premise appears. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

variable {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ}
    {owner : ι ↪ Fin N} {k : ℝ}

/-- The actual old nodes as an ordered two-level system. -/
def refinedIncidentSourceNodeSystem
    (Q : FiniteLinkComplementRefinement u owner k) (hu : StrictMono u) :
    FiniteRefinedNodeSystem Q.count where
  coarse := u
  coarse_strict := hu
  node := Q.node
  node_strict := Q.strictMono
  first := Q.first
  last := Q.last

/-- The actual target nodes, constructed from conserved coarse widths. -/
def refinedIncidentTargetNodeSystem
    (Q : FiniteLinkComplementRefinement u owner k) (hk : 0 < k)
    (width : Fin N → ℝ) (hw : ∀ j, 0 < width j)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc)) :
    FiniteRefinedNodeSystem Q.count where
  coarse := fun j ↦ linkCumulativeWidth (finiteLinkWidthSequence width) j.1
  coarse_strict := linkCumulativeWidth_strictMono (finiteLinkWidthSequence width)
    (finiteLinkWidthSequence_pos width hw)
  node := refinedIncidentTargetNode Q width
  node_strict := refinedIncidentTargetNode_strictMono Q hk width hw
  first := refinedIncidentTargetNode_first Q width
  last := refinedIncidentTargetNode_last Q width hcomp

/-- Arbitrary refined nodes have the same real-angle identifications. -/
theorem refinedIncident_node_eq_iff
    (Q : FiniteLinkComplementRefinement u owner k) (hu : StrictMono u)
    (hk : 0 < k) (width : Fin N → ℝ) (hw : ∀ j, 0 < width j)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc))
    (j l : Fin N) (i : Fin (Q.count j + 1)) (t : Fin (Q.count l + 1)) :
    Q.node j i = Q.node l t ↔
      refinedIncidentTargetNode Q width j i = refinedIncidentTargetNode Q width l t :=
  (refinedIncidentSourceNodeSystem Q hu).node_eq_iff
    (refinedIncidentTargetNodeSystem Q hk width hw hcomp) j l i t

/-- Every old boundary-ray equality is a new boundary-ray equality, and
conversely. Both radii may vary, and the common center is included. -/
theorem refinedIncident_node_polar_eq_iff
    (Q : FiniteLinkComplementRefinement u owner k) (hu : StrictMono u)
    (hu0 : u 0 = 0) (huT : u (Fin.last N) = 2 * Real.pi)
    (hk : 0 < k) (width : Fin N → ℝ) (hw : ∀ j, 0 < width j)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc))
    (htotal : (∑ j, width j) = 2 * Real.pi)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (j l : Fin N) (i : Fin (Q.count j + 1)) (t : Fin (Q.count l + 1)) :
    sectorPolar r (Q.node j i) = sectorPolar s (Q.node l t) ↔
      sectorPolar r (refinedIncidentTargetNode Q width j i) =
        sectorPolar s (refinedIncidentTargetNode Q width l t) := by
  have htargetend : linkCumulativeWidth (finiteLinkWidthSequence width) N =
      2 * Real.pi := by rw [finiteLinkWidthSequence_total, htotal]
  exact (refinedIncidentSourceNodeSystem Q hu).polar_eq_iff
    (refinedIncidentTargetNodeSystem Q hk width hw hcomp) hu0 huT
    (linkCumulativeWidth_zero (finiteLinkWidthSequence width)) htargetend hr hs j l i t

/-- Endpoint false is the lower node and endpoint true is the upper node. -/
def refinedIncidentSourceEndpoint (Q : FiniteLinkComplementRefinement u owner k)
    (x : Σ j : Fin N, Fin (Q.count j)) (top : Bool) : ℝ :=
  if top then Q.node x.1 x.2.succ else Q.node x.1 x.2.castSucc

def refinedIncidentTargetEndpoint (Q : FiniteLinkComplementRefinement u owner k)
    (width : Fin N → ℝ) (x : Σ j : Fin N, Fin (Q.count j)) (top : Bool) : ℝ :=
  if top then refinedIncidentTargetNode Q width x.1 x.2.succ
  else refinedIncidentTargetNode Q width x.1 x.2.castSucc

/-- The endpoint form consumed by actual forward and inverse branch seams.
It treats all four lower/upper endpoint combinations, including the cut ray. -/
theorem refinedIncident_boundary_seam_iff
    (Q : FiniteLinkComplementRefinement u owner k) (hu : StrictMono u)
    (hu0 : u 0 = 0) (huT : u (Fin.last N) = 2 * Real.pi)
    (hk : 0 < k) (width : Fin N → ℝ) (hw : ∀ j, 0 < width j)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc))
    (htotal : (∑ j, width j) = 2 * Real.pi)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (x y : Σ j : Fin N, Fin (Q.count j)) (b c : Bool) :
    sectorPolar r (refinedIncidentSourceEndpoint Q x b) =
        sectorPolar s (refinedIncidentSourceEndpoint Q y c) ↔
      sectorPolar r (refinedIncidentTargetEndpoint Q width x b) =
        sectorPolar s (refinedIncidentTargetEndpoint Q width y c) := by
  cases b <;> cases c <;>
    exact refinedIncident_node_polar_eq_iff Q hu hu0 huT hk width hw hcomp htotal
      hr hs x.1 y.1 _ _

/-- Distinct old refined closed wedges overlap, away from the center, only
on their explicitly indexed endpoint rays. -/
theorem refinedIncident_source_overlap_endpoints
    (Q : FiniteLinkComplementRefinement u owner k) (hu : StrictMono u)
    (hu0 : u 0 = 0) (huT : u (Fin.last N) = 2 * Real.pi)
    (x y : Σ j : Fin N, Fin (Q.count j)) (hne : x ≠ y)
    {R S : ℝ} {z : ℂ} (hz0 : z ≠ 0)
    (hzx : z ∈ flatLinkOccupiedDisk R (Q.node x.1 x.2.castSucc) (Q.node x.1 x.2.succ))
    (hzy : z ∈ flatLinkOccupiedDisk S (Q.node y.1 y.2.castSucc) (Q.node y.1 y.2.succ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ b c : Bool,
      z = sectorPolar r (refinedIncidentSourceEndpoint Q x b) ∧
      z = sectorPolar r (refinedIncidentSourceEndpoint Q y c) :=
  (refinedIncidentSourceNodeSystem Q hu).nonzero_wedge_overlap_endpoints
    hu0 huT x y hne hz0 hzx hzy

/-- The corresponding target-wedge overlap classification is constructed
from exactly the same conserved widths used by the physical branch placement. -/
theorem refinedIncident_target_overlap_endpoints
    (Q : FiniteLinkComplementRefinement u owner k)
    (hk : 0 < k) (width : Fin N → ℝ) (hw : ∀ j, 0 < width j)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc))
    (htotal : (∑ j, width j) = 2 * Real.pi)
    (x y : Σ j : Fin N, Fin (Q.count j)) (hne : x ≠ y)
    {R S : ℝ} {z : ℂ} (hz0 : z ≠ 0)
    (hzx : z ∈ flatLinkOccupiedDisk R
      (refinedIncidentTargetNode Q width x.1 x.2.castSucc)
      (refinedIncidentTargetNode Q width x.1 x.2.succ))
    (hzy : z ∈ flatLinkOccupiedDisk S
      (refinedIncidentTargetNode Q width y.1 y.2.castSucc)
      (refinedIncidentTargetNode Q width y.1 y.2.succ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ b c : Bool,
      z = sectorPolar r (refinedIncidentTargetEndpoint Q width x b) ∧
      z = sectorPolar r (refinedIncidentTargetEndpoint Q width y c) := by
  have htargetend : linkCumulativeWidth (finiteLinkWidthSequence width) N =
      2 * Real.pi := by rw [finiteLinkWidthSequence_total, htotal]
  exact (refinedIncidentTargetNodeSystem Q hk width hw hcomp).nonzero_wedge_overlap_endpoints
    (linkCumulativeWidth_zero (finiteLinkWidthSequence width)) htargetend x y hne hz0 hzx hzy

end RepulsiveCoulomb
