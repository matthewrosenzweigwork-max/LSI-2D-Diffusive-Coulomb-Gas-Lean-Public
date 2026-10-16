module

public import LeanResearch.RepulsiveCoulomb.PointIncidentTransitionOnCells
public import LeanResearch.RepulsiveCoulomb.EuclideanShortWedgeInterior
public import LeanResearch.RepulsiveCoulomb.FiniteEuclideanMotionPasteRigidity

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Rigidity at genuine selected-sector seams.
Recenter in the actual constructed incident chart. Each literal short target
wedge carries one motion, obtained from the actual strict-cell classification
and connected open-germ propagation. Continuity fills its boundary. Finite
closed-cover unit bounds in both directions then exclude folds and give one
motion germ at the recentered point. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb
namespace PointConstructedIncidentSurgeryChart

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

/-- Any actual local model containing this incident center agrees with its
constructed incident chart up to one actual Euclidean-motion germ. -/
theorem exists_model_rigid_germ_at_center
    (C : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (D : PointFiniteSurgeryLocalModel ha L q c hc hc1)
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0)
    (hpD : p ∈ D.chart.source) :
    ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[𝓝 p] (fun z ↦ e (C.chart z)) := by
  classical
  let T := C.chart.symm.trans D.chart
  have h0C : 0 ∈ C.chart.target := C.center ▸ C.chart.map_source C.center_mem
  have hC0 : C.chart.symm 0 = p := by
    rw [← C.center]
    exact C.chart.left_inv C.center_mem
  have h0T : 0 ∈ T.source := by
    change 0 ∈ C.chart.target ∧ C.chart.symm 0 ∈ D.chart.source
    exact ⟨h0C, hC0.symm ▸ hpD⟩
  obtain ⟨δ, hδ, hδsource⟩ := Metric.mem_nhds_iff.mp (T.open_source.mem_nhds h0T)
  let R := min δ C.ε / 2
  have hmin : 0 < min δ C.ε := lt_min hδ C.ε_pos
  have hR : 0 < R := half_pos hmin
  have hRδ : R < δ := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hRε : R < C.ε := (half_lt_self hmin).trans_le (min_le_right _ _)
  let σ := Σ j : Fin C.N, Fin (C.refinement.count j)
  let W : σ → Set ℂ := fun i ↦ flatLinkOccupiedDisk R
    (refinedIncidentTargetNode C.refinement C.width i.1 i.2.castSucc)
    (refinedIncidentTargetNode C.refinement C.width i.1 i.2.succ)
  have hWsource : ∀ i, W i ⊆ T.source := by
    intro i z hz
    obtain ⟨r, hr, θ, _, he⟩ := hz
    apply hδsource
    change dist z 0 < δ
    rw [dist_zero_right, he, sectorPolar_norm hr.1]
    exact hr.2.trans_lt hRδ
  have hpieces : ∀ i : σ, ∃ e : ℂ ≃ᵢ ℂ, EqOn T e (W i) := by
    intro i
    have hwidth := C.target_cell_width_bounds i
    have hclosure : closure (interior (W i)) = W i :=
      flatLinkOccupiedDisk_closure_interior hR hwidth.1 hwidth.2
    have hcont : ContinuousOn T (closure (interior (W i))) := by
      rw [hclosure]
      exact T.continuousOn.mono (hWsource i)
    obtain ⟨e, he⟩ := exists_euclideanMotion_eqOn_closure_of_local_germs
      isOpen_interior
      (flatLinkOccupiedDisk_interior_preconnected hR hwidth.1 hwidth.2)
      (flatLinkOccupiedDisk_interior_nonempty hR hwidth.1 hwidth.2) T hcont (by
        intro z hz
        obtain ⟨r, hr, θ, hθ, he⟩ :=
          flatLinkOccupiedDisk_interior_strict_polar hR hwidth.1 hwidth.2 hz
        have hzD : C.chart.symm z ∈ D.chart.source := (hWsource i (interior_subset hz)).2
        rw [he] at hzD ⊢
        exact C.transition_germ_on_strict_target_cell D hdis hregular i hr.1
          (hr.2.trans hRε) hθ hzD)
    exact ⟨e, hclosure ▸ he⟩
  choose motion hmotion using hpieces
  have hsource : ball (0 : ℂ) R ⊆ T.source :=
    fun z hz ↦ hδsource (hz.trans hRδ)
  have hclosed : ∀ i, IsClosed {z : ball (0 : ℂ) R | z.1 ∈ W i} := fun i ↦
    (flatLinkOccupiedDisk_isClosed R
      (refinedIncidentTargetNode C.refinement C.width i.1 i.2.castSucc)
      (refinedIncidentTargetNode C.refinement C.width i.1 i.2.succ)).preimage continuous_subtype_val
  have hcover : ∀ z ∈ ball (0 : ℂ) R, ∃ i, z ∈ W i := by
    intro z hz
    have hn : ‖z‖ ≤ R := by
      have hzNorm : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
      exact hzNorm.le
    exact refinedIncidentTargetWedges_cover C.N_pos C.refinement C.width
      C.width_complement C.width_total R hn
  obtain ⟨e, he⟩ := exists_euclideanMotion_germ_of_finite_piecewise_motions T hR hsource
    W hclosed hcover motion (fun i z _ hz ↦ hmotion i hz)
  have he' : (T : ℂ → ℂ) =ᶠ[𝓝 (C.chart p)] (e : ℂ → ℂ) := by
    simpa only [C.center] using he
  have hcomp := (C.chart.continuousAt C.center_mem).eventually he'
  refine ⟨e, ?_⟩
  filter_upwards [hcomp, C.chart.open_source.mem_nhds C.center_mem] with z hz hzC
  change D.chart (C.chart.symm (C.chart z)) = e (C.chart z) at hz
  simpa only [C.chart.left_inv hzC] using hz

end PointConstructedIncidentSurgeryChart

namespace PointFiniteSurgeryLocalModel
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p q : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

/-- Full actual local overlap rigidity. The chart data are the constructed
sector-interior, unchanged and incident cases, and the pointwise exact
budget constructs the necessary recentered model. The desired Euclidean
motion is an output, not an atlas/transition hypothesis. -/
theorem exists_rigid_overlap
    (D : PointFiniteSurgeryLocalModel ha L p c hc hc1)
    (E : PointFiniteSurgeryLocalModel ha L q c hc hc1)
    (hdis : L.Pairwise (fun S F ↦ Disjoint S.openImage F.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0)
    (x : ℂ)
    (hbalance : (1-c) * pointActualAllocatedBudget L x = Real.pi * coalescedPointExponent a y x)
    (hxD : x ∈ D.chart.source) (hxE : x ∈ E.chart.source) :
    ∃ e : ℂ ≃ᵢ ℂ, (D.chart : ℂ → ℂ) =ᶠ[𝓝 x] (fun z ↦ e (E.chart z)) := by
  classical
  by_cases hselected : ∃ i : Fin L.length, x ∈ (L.get i).openImage
  · obtain ⟨i, hi⟩ := hselected
    have hopen := pointFlatEmbedding_isOpen_openImage ha y (L.get i).map (L.get i).metric
      (hregular _ (List.get_mem L i))
    exact D.exists_rigid_overlap_of_mem_openImage E hdis i hopen x hxD hxE hi
  have hseam : ∀ i : Fin L.length, x ∉ (L.get i).openImage := fun i hi ↦ hselected ⟨i, hi⟩
  by_cases hincident : ∃ i : Fin L.length, x ∈ range (L.get i).map
  · obtain ⟨i, hi⟩ := hincident
    obtain ⟨C⟩ := exists_pointConstructedIncidentSurgeryChart ha y L x hc hc1
      hdis hregular hbalance hseam ⟨i, hi⟩
    obtain ⟨d, hd⟩ := C.exists_model_rigid_germ_at_center D hdis hregular hxD
    obtain ⟨e, he⟩ := C.exists_model_rigid_germ_at_center E hdis hregular hxE
    refine ⟨e.symm.trans d, ?_⟩
    filter_upwards [hd, he] with z hdz hez
    rw [hdz, hez]
    exact (congrArg d (e.symm_apply_apply _)).symm
  · exact D.exists_rigid_overlap_of_no_selected_range E x hxD hxE (fun i hi ↦ hincident ⟨i, hi⟩)

end PointFiniteSurgeryLocalModel
end RepulsiveCoulomb
