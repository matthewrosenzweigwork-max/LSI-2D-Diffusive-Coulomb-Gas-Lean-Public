import LeanResearch.RepulsiveCoulomb.PointConstructedIncidentSurgeryChart
import LeanResearch.RepulsiveCoulomb.FiniteClosedPieceMetricBounds

/-! SOURCE-ONLY, UNCOMPILED. Cross-piece bounds for the actual incident
chart. Forward estimates are centered local estimates on the genuine open
source; the inverse globalizes on its actual convex target disk. No source
convexity or finite bound on the number of seam crossings is asserted. -/
noncomputable section
open Set Metric Filter
open scoped Topology
open scoped NNReal
namespace RepulsiveCoulomb

theorem finiteClosedFamily_eventually_incident_on_open
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (S : ι → Set X)
    (hclosed : ∀ i, IsClosed {z : U | z.1 ∈ S i})
    (x : X) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, y ∈ U ∧ ∀ i, y ∈ S i → x ∈ S i := by
  rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨x, hx⟩ : U)]
  have h := finiteClosedFamily_eventually_incident
    (fun i ↦ {z : U | z.1 ∈ S i}) hclosed (⟨x, hx⟩ : U)
  change ∀ᶠ y : U in 𝓝 (⟨x, hx⟩ : U), y.1 ∈ U ∧ ∀ i, y.1 ∈ S i → x ∈ S i
  filter_upwards [h] with y hy
  exact ⟨y.2, hy⟩

namespace PointConstructedIncidentSurgeryChart
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

theorem source_piece_isClosed (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (i : Σ j : Fin D.N, Fin (D.refinement.count j)) :
    IsClosed {z : D.chart.source | z.1 ∈
      pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius D.refinement i} := by
  let C := D.data.cone.rotate (-D.data.lo D.initial)
  let f : D.chart.source → pointConeOpenBall C D.data.radius := fun z ↦ ⟨z.1, D.source_subset z.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact (pointConeBallAngularPiece_isClosed C D.data.radius
    (D.refinement.node i.1 i.2.castSucc) (D.refinement.node i.1 i.2.succ)).preimage hf

theorem source_piece_cover (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (z : ℂ) (hz : z ∈ D.chart.source) :
    ∃ i : (Σ j : Fin D.N, Fin (D.refinement.count j)), z ∈
      pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius D.refinement i := by
  have hn : ‖(D.data.cone.rotate (-D.data.lo D.initial)).chart z‖ ≤ D.data.radius := by
    have h : dist ((D.data.cone.rotate (-D.data.lo D.initial)).chart z) 0 <
        D.data.radius := (D.source_subset hz).2
    simpa only [dist_zero_right] using h.le
  exact finiteLinkComplementRefinement_whole_source_cover D.N_pos D.u_first D.u_last
    D.refinement D.data.radius hn

theorem centered_forward_bound (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : ℂ) (hx : x ∈ D.chart.source) :
    ∀ᶠ z in 𝓝 x, dist (D.chart x) (D.chart z) ≤ (pointSmoothConformalEDist a y x z).toReal := by
  let S := pointRefinedSourceSet (D.data.cone.rotate (-D.data.lo D.initial)) D.data.radius D.refinement
  filter_upwards [finiteClosedFamily_eventually_incident_on_open D.chart.source
    D.chart.open_source S D.source_piece_isClosed x hx] with z hz
  obtain ⟨i, hi⟩ := D.source_piece_cover z hz.1
  have hix := hz.2 i hi
  rw [D.forward_formula i x hx hix, D.forward_formula i z hz.1 hi]
  exact ((D.bounds i).1 x ⟨D.source_subset hx, hix⟩ z ⟨D.source_subset hz.1, hi⟩).2

/-- The inverse estimate is genuinely cross-piece on the entire new disk. -/
theorem inverse_global_bound (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (z w : ℂ) (hz : z ∈ ball 0 D.ε) (hw : w ∈ ball 0 D.ε) :
    c * (pointSmoothConformalEDist a y (D.chart.symm z) (D.chart.symm w)).toReal ≤ dist z w := by
  let old := pointSmoothConformalMetricSpace ha y
  let K : ℝ≥0 := ⟨1 / c, le_of_lt (one_div_pos.mpr hc)⟩
  let T := pointRefinedTargetSet D.ε D.refinement D.width
  have hclosed : ∀ i, IsClosed {z : ball (0 : ℂ) D.ε | z.1 ∈ T i} := fun i ↦
    (flatLinkOccupiedDisk_isClosed D.ε
      (refinedIncidentTargetNode D.refinement D.width i.1 i.2.castSucc)
      (refinedIncidentTargetNode D.refinement D.width i.1 i.2.succ)).preimage continuous_subtype_val
  have hcover : ∀ z ∈ ball (0 : ℂ) D.ε, ∃ i, z ∈ T i := by
    intro z hz
    have hn : ‖z‖ ≤ D.ε := by
      have hh : dist z 0 < D.ε := hz
      simpa only [dist_zero_right] using hh.le
    exact refinedIncidentTargetWedges_cover D.N_pos D.refinement D.width
      D.width_complement D.width_total D.ε hn
  have h := @lipschitzOnWith_of_finite_closed_cover_of_convex
    (Σ j : Fin D.N, Fin (D.refinement.count j)) ℂ ℂ inferInstance inferInstance inferInstance
    old.toPseudoMetricSpace K D.chart.symm (ball 0 D.ε) (convex_ball _ _) T hclosed hcover (by
      intro i
      apply (@lipschitzOnWith_iff_dist_le_mul ℂ ℂ
        (inferInstance : PseudoMetricSpace ℂ) old.toPseudoMetricSpace K
        (ball 0 D.ε ∩ T i) D.chart.symm).mpr
      intro z hz w hw
      change (pointSmoothConformalEDist a y (D.chart.symm z) (D.chart.symm w)).toReal ≤
        (1 / c) * dist z w
      rw [D.inverse_formula i z hz.1 hz.2, D.inverse_formula i w hw.1 hw.2]
      have hb := ((D.bounds i).2 z hz w hw).1
      have hd := (le_div_iff₀ hc).mpr (show
        (pointSmoothConformalEDist a y ((D.branch i).inverse z) ((D.branch i).inverse w)).toReal * c ≤ dist z w by
          simpa only [mul_comm] using hb)
      simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one, one_mul] using hd)
  have hb := (@lipschitzOnWith_iff_dist_le_mul ℂ ℂ
    (inferInstance : PseudoMetricSpace ℂ) old.toPseudoMetricSpace K
    (ball 0 D.ε) D.chart.symm).mp h z hz w hw
  change (pointSmoothConformalEDist a y (D.chart.symm z) (D.chart.symm w)).toReal ≤
    (1 / c) * dist z w at hb
  calc
    c * (pointSmoothConformalEDist a y (D.chart.symm z) (D.chart.symm w)).toReal ≤
        c * ((1 / c) * dist z w) := mul_le_mul_of_nonneg_left hb hc.le
    _ = dist z w := by field_simp [hc.ne']

theorem global_lower_bound (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (z w : ℂ) (hz : z ∈ D.chart.source) (hw : w ∈ D.chart.source) :
    c * (pointSmoothConformalEDist a y z w).toReal ≤ dist (D.chart z) (D.chart w) := by
  have hzT : D.chart z ∈ ball 0 D.ε := D.target ▸ D.chart.map_source hz
  have hwT : D.chart w ∈ ball 0 D.ε := D.target ▸ D.chart.map_source hw
  simpa only [D.chart.left_inv hz, D.chart.left_inv hw] using
    D.inverse_global_bound (D.chart z) (D.chart w) hzT hwT

end PointConstructedIncidentSurgeryChart
end RepulsiveCoulomb
