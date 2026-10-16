import LeanResearch.RepulsiveCoulomb.PointSurgeryInteriorOverlap
import LeanResearch.RepulsiveCoulomb.PointSurgeryUnselectedOverlap
import LeanResearch.RepulsiveCoulomb.PointIncidentStrictCellClassification
import LeanResearch.RepulsiveCoulomb.PointIncidentTargetCellWidths

/-! SOURCE-ONLY, UNCOMPILED. Actual recentered transitions have Euclidean
motion germs on every strict target cell. Occupied cells use the same global
selected-sector contraction; complement cells use the original local metric.
No transition assumption is fed into either case. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb
namespace PointConstructedIncidentSurgeryChart

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

/-- Interior rigidity in literal recentered target coordinates. -/
theorem transition_germ_on_strict_target_cell
    (C : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (D : PointFiniteSurgeryLocalModel ha L q c hc hc1)
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0)
    (i : Σ j : Fin C.N, Fin (C.refinement.count j)) {r θ : ℝ}
    (hr : 0 < r) (hrε : r < C.ε)
    (hθ : θ ∈ Ioo
      (refinedIncidentTargetNode C.refinement C.width i.1 i.2.castSucc)
      (refinedIncidentTargetNode C.refinement C.width i.1 i.2.succ))
    (hD : C.chart.symm (sectorPolar r θ) ∈ D.chart.source) :
    ∃ e : ℂ ≃ᵢ ℂ, (fun z ↦ D.chart (C.chart.symm z)) =ᶠ[𝓝 (sectorPolar r θ)]
      (e : ℂ → ℂ) := by
  let z := sectorPolar r θ
  let w := C.chart.symm z
  have hzball : z ∈ ball (0 : ℂ) C.ε := by
    change dist (sectorPolar r θ) 0 < C.ε
    rwa [dist_zero_right, sectorPolar_norm hr.le]
  have hzT : z ∈ C.chart.target := C.target.symm ▸ hzball
  have hwC : w ∈ C.chart.source := C.chart.map_target hzT
  have hrigid : ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[𝓝 w]
      (fun v ↦ e (C.chart v)) := by
    by_cases hi : i.1 ∈ range C.owner
    · obtain ⟨j, hj⟩ := hi
      have hij : i = C.occupiedCell j := C.eq_occupiedCell_of_fst_eq i j hj.symm
      have hθj : θ ∈ Ioo
          (refinedIncidentTargetNode C.refinement C.width
            (C.occupiedCell j).1 (C.occupiedCell j).2.castSucc)
          (refinedIncidentTargetNode C.refinement C.width
            (C.occupiedCell j).1 (C.occupiedCell j).2.succ) := hij ▸ hθ
      have hwopen := C.occupied_target_strict_mem_openImage j hr hrε hθj
      have hopen : IsOpen (L.get j.1).openImage :=
        pointFlatEmbedding_isOpen_openImage ha y (L.get j.1).map (L.get j.1).metric
          (hregular _ (List.get_mem L j.1))
      exact D.exists_rigid_overlap_of_mem_openImage (.incident C) hdis j.1 hopen w hD hwC hwopen
    · exact D.exists_rigid_overlap_of_no_selected_range (.incident C) w hD hwC
        (C.complement_target_strict_not_mem_range i hi hr hrε hθ)
  obtain ⟨e, he⟩ := hrigid
  have hcomp := (C.chart.symm.continuousAt hzT).eventually he
  refine ⟨e, ?_⟩
  filter_upwards [hcomp, C.chart.open_target.mem_nhds hzT] with v hv hvT
  simpa only [C.chart.right_inv hvT] using hv

end PointConstructedIncidentSurgeryChart
end RepulsiveCoulomb
