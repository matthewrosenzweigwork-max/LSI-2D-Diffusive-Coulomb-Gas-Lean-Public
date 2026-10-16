module

public import LeanResearch.RepulsiveCoulomb.PointComplementCellSectorExclusion
public import LeanResearch.RepulsiveCoulomb.PointIncidentOccupiedMotion

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Strict refined-cell classification.

Strict source complement cells miss all selected closed sector ranges.
Strict target occupied cells return to the actual selected open image under
the constructed inverse chart. These are geometric consequences of ordered
nodes, the physical branch laws, and actual sector contraction coordinates.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

namespace FiniteRefinedNodeSystem
variable {N : ℕ} {count : Fin N → ℕ}

/-- A positive-radius point at a strict cell angle belongs to no other
closed wedge. The proof explicitly excludes the cyclic 0/2*pi identification. -/
theorem strict_polar_not_mem_other_wedge (P : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (x y : Σ j : Fin N, Fin (count j)) (hxy : x ≠ y)
    {r θ R : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Ioo (P.cellLower x) (P.cellUpper x)) :
    sectorPolar r θ ∉ flatLinkOccupiedDisk R (P.cellLower y) (P.cellUpper y) := by
  rintro ⟨s, hs, φ, hφ, he⟩
  have hrs : r = s := by
    have hn := congrArg norm he
    simpa only [sectorPolar_norm hr.le, sectorPolar_norm hs.1] using hn
  subst s
  have hlo := P.node_mem_global x.1 x.2.castSucc
  have hhi := P.node_mem_global x.1 x.2.succ
  rw [hP0, hPT] at hlo hhi
  have hθglobal : θ ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨hlo.1.trans_lt hθ.1, hθ.2.trans_le hhi.2⟩
  have hφglobal := P.cell_mem_global hP0 hPT y hφ
  rcases (sectorPolar_eq_iff_closed_period hr
    ⟨hθglobal.1.le, hθglobal.2.le⟩ hφglobal).mp he with hsame | ⟨hzero, _⟩ | ⟨hperiod, _⟩
  · subst φ
    rcases P.cells_separated x y hxy with hsep | hsep
    · linarith [hθ.2, hφ.1]
    · linarith [hφ.2, hθ.1]
  · exact (ne_of_gt hθglobal.1) hzero
  · exact (ne_of_lt hθglobal.2) hperiod

/-- A strict cell point is unequal to either endpoint ray, even when the
endpoint's radial parameter is independently chosen. -/
theorem strict_polar_ne_cell_endpoint (P : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (x : Σ j : Fin N, Fin (count j)) {r s θ : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hθ : θ ∈ Ioo (P.cellLower x) (P.cellUpper x)) (top : Bool) :
    sectorPolar r θ ≠ sectorPolar s (P.cellEndpoint x top) := by
  intro he
  have hrs : r = s := by
    have hn := congrArg norm he
    simpa only [sectorPolar_norm hr.le, sectorPolar_norm hs] using hn
  subst s
  have hlo := P.node_mem_global x.1 x.2.castSucc
  have hhi := P.node_mem_global x.1 x.2.succ
  rw [hP0, hPT] at hlo hhi
  have hθglobal : θ ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨hlo.1.trans_lt hθ.1, hθ.2.trans_le hhi.2⟩
  have hendglobal : P.cellEndpoint x top ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    cases top
    · exact hlo
    · exact hhi
  rcases (sectorPolar_eq_iff_closed_period hr
    ⟨hθglobal.1.le, hθglobal.2.le⟩ hendglobal).mp he with hsame | ⟨hzero, _⟩ | ⟨hperiod, _⟩
  · cases top
    · exact (ne_of_gt hθ.1) hsame
    · exact (ne_of_lt hθ.2) hsame
  · exact (ne_of_gt hθglobal.1) hzero
  · exact (ne_of_lt hθglobal.2) hperiod

end FiniteRefinedNodeSystem

/-- Inverting the literal directed placement carries a strict ordered
target angle to the interior of the canonical Euclidean sector, for either
orientation. -/
theorem directedSectorPlacement_symm_strict_mem_interior {β r θ lo : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hr : 0 < r)
    (hθ : θ ∈ Ioo lo (lo + β)) (forward : Bool) :
    (directedSectorPlacement lo β forward).symm (sectorPolar r θ) ∈
      interior (closedEuclideanSector β) := by
  let φ := if forward then θ - lo else β - (θ - lo)
  have hφ : φ ∈ Ioo (0 : ℝ) β := by
    cases forward <;> simp only [φ, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [hθ.1, hθ.2]
  have hplaced : directedSectorPlacement lo β forward (sectorPolar r φ) =
      sectorPolar r θ := by
    rw [directedSectorPlacement_polar]
    congr 1
    cases forward <;> simp only [φ, Bool.false_eq_true, ↓reduceIte] <;> ring
  have hinverse : (directedSectorPlacement lo β forward).symm (sectorPolar r θ) =
      sectorPolar r φ := by
    rw [← hplaced, (directedSectorPlacement lo β forward).symm_apply_apply]
  rw [hinverse]
  apply mem_interior_closedEuclideanSector_of_strict_arg hβ hβπ
  rw [sectorPolar_arg hr ⟨by linarith [hφ.1, Real.pi_pos], hφ.2.le.trans hβπ⟩]
  exact hφ

namespace PointConstructedIncidentSurgeryChart
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {p : ℂ} {c : ℝ} {hc : 0 < c} {hc1 : c ≤ 1}

/-- Strict angular interiors of actual complement cells avoid the whole
closed range of every selected sector, not merely its open image. -/
theorem complement_source_strict_not_mem_range
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : Σ j : Fin D.N, Fin (D.refinement.count j))
    (hx : x.1 ∉ range D.owner) {z : ℂ} {r θ : ℝ}
    (hz : z ∈ pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius)
    (hr : r ∈ Ioo (0 : ℝ) D.data.radius)
    (hθ : θ ∈ Ioo (D.refinement.node x.1 x.2.castSucc)
      (D.refinement.node x.1 x.2.succ))
    (he : (D.data.cone.rotate (-D.data.lo D.initial)).chart z = sectorPolar r θ) :
    ∀ i : Fin L.length, z ∉ range (L.get i).map := by
  let P := refinedIncidentSourceNodeSystem D.refinement D.u_mono
  intro i hzi
  let j : PointIncidentIndex L p := ⟨i, D.incident_of_mem_range i z hz hzi⟩
  have hxj : x ≠ D.occupiedCell j := by
    intro hh
    apply hx
    exact ⟨j, (congrArg Sigma.fst hh).symm⟩
  have hcell := (D.occupied_cell_iff j z hz).mpr hzi
  change (D.data.cone.rotate (-D.data.lo D.initial)).chart z ∈
    flatLinkOccupiedDisk D.data.radius
      (P.cellLower (D.occupiedCell j)) (P.cellUpper (D.occupiedCell j)) at hcell
  rw [he] at hcell
  exact P.strict_polar_not_mem_other_wedge D.u_first D.u_last x
    (D.occupiedCell j) hxj hr.1 hθ hcell

/-- The exact target nodes of an occupied cell retain the physical new
patch angle; no target interpolation is substituted for that patch. -/
theorem occupied_target_nodes
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (i : PointIncidentIndex L p) :
    refinedIncidentTargetNode D.refinement D.width
        (D.occupiedCell i).1 (D.occupiedCell i).2.castSucc =
      linkCumulativeWidth (finiteLinkWidthSequence D.width) (D.owner i).1 ∧
    refinedIncidentTargetNode D.refinement D.width
        (D.occupiedCell i).1 (D.occupiedCell i).2.succ =
      linkCumulativeWidth (finiteLinkWidthSequence D.width) (D.owner i).1 +
        (D.data.paired i).new.angle := by
  have howned : D.owner i ∈ range D.owner := mem_range_self i
  constructor
  · change refinedIncidentTargetNode D.refinement D.width (D.owner i) 0 = _
    exact refinedIncidentTargetNode_first D.refinement D.width (D.owner i)
  · simp only [occupiedCell, refinedIncidentTargetNode, if_pos howned,
      Fin.val_succ, Nat.zero_add, Nat.cast_one, one_mul, D.width_owned i]

/-- A point strictly inside an occupied target wedge returns under the
actual pasted inverse to the original owner's selected open image. -/
theorem occupied_target_strict_mem_openImage
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (i : PointIncidentIndex L p) {r θ : ℝ}
    (hr : 0 < r) (hrε : r < D.ε)
    (hθ : θ ∈ Ioo
      (refinedIncidentTargetNode D.refinement D.width
        (D.occupiedCell i).1 (D.occupiedCell i).2.castSucc)
      (refinedIncidentTargetNode D.refinement D.width
        (D.occupiedCell i).1 (D.occupiedCell i).2.succ)) :
    D.chart.symm (sectorPolar r θ) ∈ (L.get i.1).openImage := by
  let B := D.data.paired i
  let lo := linkCumulativeWidth (finiteLinkWidthSequence D.width) (D.owner i).1
  let forward := D.data.forward i
  let z := sectorPolar r θ
  let w := D.chart.symm z
  have hθ' : θ ∈ Ioo lo (lo + B.new.angle) := by
    simpa only [(D.occupied_target_nodes i).1, (D.occupied_target_nodes i).2] using hθ
  have hzball : z ∈ ball (0 : ℂ) D.ε := by
    change dist (sectorPolar r θ) 0 < D.ε
    rwa [dist_zero_right, sectorPolar_norm hr.le]
  have hzcell : z ∈ pointRefinedTargetSet D.ε D.refinement D.width (D.occupiedCell i) :=
    ⟨r, ⟨hr.le, hrε.le⟩, θ, ⟨hθ.1.le, hθ.2.le⟩, rfl⟩
  have hwsource : w ∈
      pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius ∩
      pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial))
        D.data.radius D.refinement (D.occupiedCell i) := by
    dsimp only [w]
    rw [D.inverse_formula (D.occupiedCell i) z hzball hzcell]
    exact (D.branch (D.occupiedCell i)).inverse_source z ⟨hzball, hzcell⟩
  have hwR : w ∈ range (L.get i.1).map :=
    (D.occupied_cell_iff i w hwsource.1).mp hwsource.2
  have hforward : (D.branch (D.occupiedCell i)).forward w = z := by
    dsimp only [w]
    rw [D.inverse_formula (D.occupiedCell i) z hzball hzcell]
    exact (D.branch (D.occupiedCell i)).right_inv z ⟨hzball, hzcell⟩
  rw [D.occupied_branch_formula i,
    B.occupiedForward_eq ha hc hc1 lo forward hwR] at hforward
  let u := (L.get i.1).localForward ha hc hc1 B.new ⟨w, hwR⟩
  have hu : u = (directedSectorPlacement lo B.new.angle forward).symm z := by
    apply (directedSectorPlacement lo B.new.angle forward).injective
    rw [(directedSectorPlacement lo B.new.angle forward).apply_symm_apply]
    exact hforward
  have huinterior : u ∈ interior (closedEuclideanSector B.new.angle) := by
    rw [hu]
    exact directedSectorPlacement_symm_strict_mem_interior B.new.angle_pos
      B.new.angle_le_pi hr hθ' forward
  have hεnew : D.ε ≤ B.new.radius :=
    D.ε_le.trans ((mul_le_of_le_one_left D.data.radius_pos.le hc1).trans
      (D.data.radius_new i))
  have hunorm : ‖u‖ < B.new.radius := by
    rw [hu, directedSectorPlacement_symm_norm]
    change ‖sectorPolar r θ‖ < B.new.radius
    rw [sectorPolar_norm hr.le]
    exact hrε.trans_le hεnew
  let q : flatLinkSectorDisk B.new.angle B.new.radius :=
    ⟨u, interior_subset huinterior, hunorm.le⟩
  have hnew := B.new.inclusion_mem_interior q huinterior hunorm
  apply (pointActualSectorContractionChart_interior_iff ha (L.get i.1) hc hc1 ⟨w, hwR⟩).mpr
  change B.new.placement (B.new.placement.symm
    (pointActualSectorContractionChart ha (L.get i.1) hc hc1 ⟨w, hwR⟩ : ℂ)) ∈
      interior (closedEuclideanSector (c * (L.get i.1).beta)) at hnew
  rwa [B.new.placement.apply_symm_apply] at hnew

/-- Strict target complement points return outside every selected closed
sector. A hypothetical incident closed-range intersection would force a
source endpoint, whose actual branch formula forces a forbidden target
endpoint. Thus no radial formula for an occupied branch is assumed. -/
theorem complement_target_strict_not_mem_range
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : Σ j : Fin D.N, Fin (D.refinement.count j))
    (hx : x.1 ∉ range D.owner) {r θ : ℝ}
    (hr : 0 < r) (hrε : r < D.ε)
    (hθ : θ ∈ Ioo
      (refinedIncidentTargetNode D.refinement D.width x.1 x.2.castSucc)
      (refinedIncidentTargetNode D.refinement D.width x.1 x.2.succ)) :
    ∀ i : Fin L.length, D.chart.symm (sectorPolar r θ) ∉ range (L.get i).map := by
  let C := D.data.cone.rotate (-D.data.lo D.initial)
  let z := sectorPolar r θ
  let w := D.chart.symm z
  have hk : 0 < coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  let P := refinedIncidentTargetNodeSystem D.refinement hk D.width
    D.width_pos D.width_complement
  have hP0 : P.coarse 0 = 0 := linkCumulativeWidth_zero (finiteLinkWidthSequence D.width)
  have hPT : P.coarse (Fin.last D.N) = 2 * Real.pi := by
    change linkCumulativeWidth (finiteLinkWidthSequence D.width) D.N = 2 * Real.pi
    rw [finiteLinkWidthSequence_total, D.width_total]
  have hzball : z ∈ ball (0 : ℂ) D.ε := by
    change dist (sectorPolar r θ) 0 < D.ε
    rwa [dist_zero_right, sectorPolar_norm hr.le]
  have hzcell : z ∈ pointRefinedTargetSet D.ε D.refinement D.width x :=
    ⟨r, ⟨hr.le, hrε.le⟩, θ, ⟨hθ.1.le, hθ.2.le⟩, rfl⟩
  have hwsource : w ∈ pointConeOpenBall C D.data.radius ∩
      pointRefinedSourceSet C D.data.radius D.refinement x := by
    dsimp only [w]
    rw [D.inverse_formula x z hzball hzcell]
    exact (D.branch x).inverse_source z ⟨hzball, hzcell⟩
  have hforward : (D.branch x).forward w = z := by
    dsimp only [w]
    rw [D.inverse_formula x z hzball hzcell]
    exact (D.branch x).right_inv z ⟨hzball, hzcell⟩
  have hnotendpoint (s : ℝ) (hs : 0 ≤ s) (top : Bool) :
      C.chart w ≠ sectorPolar s (refinedIncidentSourceEndpoint D.refinement x top) := by
    intro he
    have hh := (D.branch x).forward_endpoint w hwsource s hs top he
    rw [hforward] at hh
    exact P.strict_polar_ne_cell_endpoint hP0 hPT x hr hs hθ top hh
  have hw0 : C.chart w ≠ 0 := by
    intro hzero
    apply hnotendpoint 0 le_rfl false
    simpa only [sectorPolar_zero] using hzero
  intro i hwi
  let j : PointIncidentIndex L p := ⟨i, D.incident_of_mem_range i w hwsource.1 hwi⟩
  have hxj : x ≠ D.occupiedCell j := by
    intro he
    apply hx
    exact ⟨j, (congrArg Sigma.fst he).symm⟩
  have hoccupied := (D.occupied_cell_iff j w hwsource.1).mpr hwi
  obtain ⟨s, hs, top, other, he, _⟩ := refinedIncident_source_overlap_endpoints
    D.refinement D.u_mono D.u_first D.u_last x (D.occupiedCell j) hxj hw0
    hwsource.2 hoccupied
  exact hnotendpoint s hs.le top he

end PointConstructedIncidentSurgeryChart
end RepulsiveCoulomb
