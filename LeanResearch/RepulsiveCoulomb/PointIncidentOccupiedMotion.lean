module

public import LeanResearch.RepulsiveCoulomb.PointConstructedIncidentSurgeryChart
public import LeanResearch.RepulsiveCoulomb.PointFiniteSurgeryAllPointCharts

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The actual occupied pieces retain their exact
motion relative to the original global sector contraction. These formulas
hold on the full closed sector range inside the constructed chart, including
its seams. No rigidity or transition certificate is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb
namespace PointConstructedIncidentSurgeryChart

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)

/-- There is exactly one refined subcell in an occupied coarse cell. -/
def occupiedCell (i : PointIncidentIndex L p) : Σ j : Fin D.N, Fin (D.refinement.count j) :=
  ⟨D.owner i, ⟨0, D.refinement.count_pos (D.owner i)⟩⟩

/-- The angular occupied cell is exactly the actual old closed sector on the
common cone ball; this identifies its full source, not just its boundary. -/
theorem occupied_cell_iff (i : PointIncidentIndex L p) (z : ℂ)
    (hz : z ∈ pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius) :
    z ∈ pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial))
      D.data.radius D.refinement (D.occupiedCell i) ↔ z ∈ range (L.get i.1).map := by
  have hcount : D.refinement.count (D.owner i) = 1 :=
    D.refinement.occupied_whole (D.owner i) (mem_range_self i)
  have hvfirst : (D.occupiedCell i).2.castSucc =
      (0 : Fin (D.refinement.count (D.owner i) + 1)) := rfl
  have hvlast : (D.occupiedCell i).2.succ = Fin.last (D.refinement.count (D.owner i)) := by
    apply Fin.ext
    change 0 + 1 = D.refinement.count (D.owner i)
    omega
  have hd := (mem_pointConeOpenBall_iff
    (D.data.cone.rotate (-D.data.lo D.initial))
    (show D.data.radius ≤ (D.data.cone.rotate (-D.data.lo D.initial)).radius from
      D.data.radius_cone) z).mp hz
  have h := (D.data.paired i).sourcePatch.rotated_normalized_range_iff ha D.data.cone
    D.data.radius_pos (D.data.radius_old i) D.data.radius_cone (D.data.polar i)
    (D.data.lo D.initial) hd.le
  change (D.data.cone.rotate (-D.data.lo D.initial)).chart z ∈
    flatLinkOccupiedDisk D.data.radius
      (D.refinement.node (D.owner i) (D.occupiedCell i).2.castSucc)
      (D.refinement.node (D.owner i) (D.occupiedCell i).2.succ) ↔ _
  rw [hvfirst, hvlast, D.refinement.first, D.refinement.last,
    (D.owner_ends i).1, (D.owner_ends i).2]
  exact h.symm

/-- Every refined index over an occupied coarse cell is its canonical
single occupied index. -/
theorem eq_occupiedCell_of_fst_eq
    (x : Σ j : Fin D.N, Fin (D.refinement.count j))
    (i : PointIncidentIndex L p) (hx : x.1 = D.owner i) : x = D.occupiedCell i := by
  rcases x with ⟨j, v⟩
  change j = D.owner i at hx
  subst j
  have hcount : D.refinement.count (D.owner i) = 1 :=
    D.refinement.occupied_whole (D.owner i) (mem_range_self i)
  have hv : v = (D.occupiedCell i).2 := by
    apply Fin.ext
    change v.1 = 0
    have hvlt := v.2
    omega
  cases hv
  rfl

/-- A refined occupied cell can only carry the provenance of its unique
owner. Thus existential assembly cannot silently substitute another sector. -/
theorem occupied_branch_formula (i : PointIncidentIndex L p) :
    (D.branch (D.occupiedCell i)).forward = (D.data.paired i).occupiedForward ha hc hc1
      (linkCumulativeWidth (finiteLinkWidthSequence D.width) (D.owner i).1)
      (D.data.forward i) := by
  rcases D.provenance (D.occupiedCell i) with ⟨j, hj, hformula⟩ | ⟨hnot, _⟩
  · have hij : i = j := D.owner.injective hj
    subst j
    exact hformula
  · exact False.elim (hnot (mem_range_self i))

/-- The full Euclidean motion from the original contracted sector into the
actual developed placement of this chart. Reflection is retained explicitly
when the old source orientation requires it. -/
def occupiedMotion (i : PointIncidentIndex L p) : ℂ ≃ᵢ ℂ :=
  (D.data.paired i).new.placement.symm.trans
    (directedSectorPlacement
      (linkCumulativeWidth (finiteLinkWidthSequence D.width) (D.owner i).1)
      (D.data.paired i).new.angle (D.data.forward i))

/-- Exact physical chart formula, valid on the whole local closed sector. -/
theorem chart_eq_occupiedMotion (i : PointIncidentIndex L p) (z : ℂ)
    (hz : z ∈ D.chart.source) (hzS : z ∈ range (L.get i.1).map) :
    D.chart z = D.occupiedMotion i
      (pointActualSectorContractionChart ha (L.get i.1) hc hc1 ⟨z, hzS⟩ : ℂ) := by
  have hcell := (D.occupied_cell_iff i z (D.source_subset hz)).mpr hzS
  rw [D.forward_formula (D.occupiedCell i) z hz hcell, D.occupied_branch_formula i,
    (D.data.paired i).occupiedForward_eq ha hc hc1 _ _ hzS]
  rfl

/-- In particular, the constructed boundary chart agrees exactly with the
sector-interior chart up to one global Euclidean motion. -/
theorem chart_eq_sectorInteriorChart (i : PointIncidentIndex L p)
    (hopen : IsOpen (L.get i.1).openImage) (z : ℂ)
    (hz : z ∈ D.chart.source) (hzS : z ∈ (L.get i.1).openImage) :
    D.chart z = D.occupiedMotion i
      (pointActualSectorInteriorOpenChart ha (L.get i.1) hc hc1 hopen z) := by
  rw [pointActualSectorInteriorOpenChart_apply ha (L.get i.1) hc hc1 hopen z hzS]
  exact D.chart_eq_occupiedMotion i z hz ((L.get i.1).openImage_subset_range hzS)

/-- The exact sector-interior formula holds as a germ on every such overlap. -/
theorem chart_eventuallyEq_sectorInteriorChart (i : PointIncidentIndex L p)
    (hopen : IsOpen (L.get i.1).openImage) (z : ℂ)
    (hz : z ∈ D.chart.source) (hzS : z ∈ (L.get i.1).openImage) :
    (D.chart : ℂ → ℂ) =ᶠ[nhds z]
      (fun w ↦ D.occupiedMotion i
        (pointActualSectorInteriorOpenChart ha (L.get i.1) hc hc1 hopen w)) := by
  filter_upwards [D.chart.open_source.mem_nhds hz, hopen.mem_nhds hzS] with w hw hwS
  exact D.chart_eq_sectorInteriorChart i hopen w hw hwS

/-- A selected sector met anywhere inside the constructed common ball must
already be incident at its center, by the radius's actual clearance. -/
theorem incident_of_mem_range (i : Fin L.length) (z : ℂ)
    (hz : z ∈ pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius)
    (hzS : z ∈ range (L.get i).map) : p ∈ range (L.get i).map := by
  by_contra hi
  have hd := (mem_pointConeOpenBall_iff
    (D.data.cone.rotate (-D.data.lo D.initial))
    (show D.data.radius ≤ (D.data.cone.rotate (-D.data.lo D.initial)).radius from
      D.data.radius_cone) z).mp hz
  exact D.data.nonincident_clear i hi z hd.le hzS

/-- The preceding germ formula does not require the caller to know in
advance which sectors are incident: the overlap itself supplies the index. -/
theorem exists_chart_eventuallyEq_sectorInteriorChart (i : Fin L.length)
    (hopen : IsOpen (L.get i).openImage) (z : ℂ)
    (hz : z ∈ D.chart.source) (hzS : z ∈ (L.get i).openImage) :
    ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[nhds z]
      (fun w ↦ e (pointActualSectorInteriorOpenChart ha (L.get i) hc hc1 hopen w)) := by
  let j : PointIncidentIndex L p :=
    ⟨i, D.incident_of_mem_range i z (D.source_subset hz)
      ((L.get i).openImage_subset_range hzS)⟩
  exact ⟨D.occupiedMotion j, D.chart_eventuallyEq_sectorInteriorChart j hopen z hz hzS⟩

/-- An occupied cell cannot enter a different selected open sector. Both the
actual closed/open separation and the nonincident clearance are used. -/
theorem occupied_cell_avoids_other_openImage
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0)
    (i : PointIncidentIndex L p) (j : Fin L.length) (hij : i.1 ≠ j) (z : ℂ)
    (hz : z ∈ pointConeOpenBall (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius)
    (hcell : z ∈ pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial))
      D.data.radius D.refinement (D.occupiedCell i)) : z ∉ (L.get j).openImage := by
  intro hzj
  have hzjR := (L.get j).openImage_subset_range hzj
  let k : PointIncidentIndex L p := ⟨j, D.incident_of_mem_range j z hz hzjR⟩
  have hik : i ≠ k := fun he ↦ hij (congrArg Subtype.val he)
  exact Set.disjoint_left.mp
    (pointAllocatedList_incident_closed_disjoint ha y L hdis hregular p i k hik)
    ((D.occupied_cell_iff i z hz).mp hcell) hzj

end PointConstructedIncidentSurgeryChart
end RepulsiveCoulomb
