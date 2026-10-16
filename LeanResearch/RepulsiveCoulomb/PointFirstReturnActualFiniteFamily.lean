import LeanResearch.RepulsiveCoulomb.PointBoundaryFiniteCoverGeometry
import LeanResearch.RepulsiveCoulomb.PointFirstReturnCapAdapter
import LeanResearch.RepulsiveCoulomb.PointFirstReturnFiniteGBData
import LeanResearch.RepulsiveCoulomb.PointRadialListSourceSlots

/-! Successor draft. Construct the actual first-return finite radial family
from the literal finite old-boundary geodesic-piece cover and stopped metric
ray. The old side need not be one ambient geodesic and may contain atoms. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The source lists are retained so later endpoint and internal-vertex
bookkeeping refers to the actual stopped ray and old boundary. -/
theorem exists_firstReturn_actual_radial_loop
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (E : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (E i).curve)
    (b r : ℝ → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hboundary : range b = frontier P)
    {z w s t : ℝ} (hzw : z < w) (hst : s ≠ t)
    (hs : b s = r z) (ht : b t = r w)
    (hd : ∀ u ∈ Icc z w, ∀ v ∈ Icc z w,
      (pointSmoothConformalEDist a y (r u) (r v)).toReal = dist u v)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P) :
    ∃ old : List (PointRadialC1PlaneArc ha y),
    ∃ fresh : List (PointRadialC1ArcPiece ha y (lineCapSegment r z w)),
      PointBoundaryRadialChainOn ha y (lineCapSegment b s t) 0 1 old ∧
      PointRadialC1ArcChain ha y (lineCapSegment r z w) 0 1 fresh ∧
      fresh ≠ [] ∧
      let L := old ++ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
      PointRadialC1PlaneChain ha y (r z) (r z) L ∧ 2 ≤ L.length ∧
      pointRadialC1PlaneCarrier L =
        range (lineCapSegment r z w) ∪ range (lineCapSegment b s t) ∧
      L.Pairwise (fun e f => Disjoint
        (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) ∧
      (∀ e ∈ L, e.HasArgumentTurn) ∧
      (∀ e ∈ L, ∀ u ∈ Ioo (0 : ℝ) 1, e.curve u ∉ pointPunctures a y) := by
  let β := lineCapSegment b s t
  let γ := lineCapSegment r z w
  have hβi : Function.Injective β := lineCapSegment_injective_of_ne hbi hst
  have hβc : Continuous β := lineCapSegment_continuous hb s t
  have hβP : ∀ u, β u ∈ frontier P := by
    intro u
    rw [← hboundary]
    exact ⟨s + u.1 * (t - s), rfl⟩
  obtain ⟨old, hold⟩ := exists_actual_old_boundary_radial_chain ha y H hP E hpieces β hβc hβi hβP
  have hneq : r z ≠ r w := by
    intro he
    have h := hd z ⟨le_rfl, hzw.le⟩ w ⟨hzw.le, le_rfl⟩
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at h
    exact hzw.ne (dist_eq_zero.mp h.symm)
  have hγd := lineCapSegment_metricOn y r hzw.le hd
  have hγi := pointConformal_geodesic_injective ha y hneq γ hγd
  obtain ⟨fresh, hfresh, _, hne, _⟩ :=
    exists_pointConformal_finite_radial_C1_arc_chain ha y hneq γ hγd
  have hβ0 : β 0 = r z := (lineCapSegment_zero b s t).trans hs
  have hβ1 : β 1 = r w := (lineCapSegment_one b s t).trans ht
  have hγ0 : γ 0 = r z := lineCapSegment_zero r z w
  have hγ1 : γ 1 = r w := lineCapSegment_one r z w
  have hmeet : range β ∩ range γ = {r z, r w} := by
    rw [inter_comm]
    exact firstReturn_oldArc_intersection hzw hboundary hs ht hgap
  have hcross := simple_bigon_halfOpen_images_disjoint hβi hγi hβ1 hγ0 hmeet
  have hI : Icc (0 : unitInterval) 1 = univ := by
    apply eq_univ_of_forall
    exact fun u => u.2
  refine ⟨old, fresh, hold, hfresh, hne, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hOld := hold.chain
    rw [hβ0, hβ1] at hOld
    have hNew : PointRadialC1PlaneChain ha y (γ 1) (γ 0)
        ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse :=
      hfresh.toPlane.reverse
    rw [hγ0, hγ1] at hNew
    exact hOld.append hNew
  · have hOld := List.length_pos_iff.mpr hold.nonempty
    have hNew := List.length_pos_iff.mpr hne
    simp only [List.length_append, List.length_reverse, List.length_map]
    omega
  · rw [pointRadialC1PlaneCarrier_append, pointRadialC1PlaneCarrier_reverse,
      hold.carrier, hfresh.toPlane_carrier (by norm_num)]
    change β '' Icc (0 : unitInterval) 1 ∪ γ '' Icc (0 : unitInterval) 1 =
      range γ ∪ range β
    simp only [hI, image_univ]
    exact union_comm _ _
  · rw [List.pairwise_append]
    refine ⟨hold.simple, hfresh.toPlane_reverse_halfOpen_pairwise hγi, ?_⟩
    intro e he f hf
    obtain ⟨f₁, hf₁, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf₁
    rw [PointRadialC1PlaneArc.reverse_halfOpen_image]
    exact hcross.mono (hold.halfOpen e he) (hfresh.reverseHalfOpen_subset_total hγi hf₀)
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hold.argument e he
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact (g.toPlane_hasArgumentTurn hneq hγ0 hγd).reverse
  · intro e he u hu
    rcases List.mem_append.mp he with he | he
    · exact hold.avoid e he u hu
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact g.curve_no_interior_puncture hγi (by constructor <;> linarith [hu.1, hu.2])

/-- The family and same-cap mixed-GB record are now outputs of the actual
stopped ray plus finite boundary cover. This removes the finite-family premise
from the previous fixed-cap GB adapter. No cap-side coefficient bound is input. -/
theorem exists_firstReturn_actual_finite_GB
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (E : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (E i).curve)
    (b r : ℝ → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hboundary : range b = frontier P)
    {z w s t : ℝ} (hzw : z < w) (hst : s ≠ t)
    (hs : b s = r z) (ht : b t = r w)
    (hd : ∀ u ∈ Icc z w, ∀ v ∈ Icc z w,
      (pointSmoothConformalEDist a y (r u) (r v)).toReal = dist u v)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (range (lineCapSegment r z w) ∪ range (lineCapSegment b s t))ᶜ)
    (hfrontU : frontier U = range (lineCapSegment r z w) ∪ range (lineCapSegment b s t))
    (hfrontV : frontier V = range (lineCapSegment r z w) ∪ range (lineCapSegment b s t)) :
    ∃ old : List (PointRadialC1PlaneArc ha y),
    ∃ fresh : List (PointRadialC1ArcPiece ha y (lineCapSegment r z w)),
      PointBoundaryRadialChainOn ha y (lineCapSegment b s t) 0 1 old ∧
      PointRadialC1ArcChain ha y (lineCapSegment r z w) 0 1 fresh ∧
      let L := old ++ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
      ∃ n : ℕ, ∃ arcs : ℕ → PointRadialC1PlaneArc ha y,
        0 < n ∧ (∀ k, arcs k ∈ L) ∧
        arcs 0 ∈ old ∧ (∃ e ∈ fresh, arcs n = e.toPlane.reverse) ∧
        (arcs 0).curve 0 = r z ∧ (arcs n).curve 1 = r z ∧
        (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) =
          range (lineCapSegment r z w) ∪ range (lineCapSegment b s t) ∧
        Nonempty (PointFirstReturnFiniteGBData ha y arcs n U V) := by
  obtain ⟨old, fresh, hold, hfresh, hfreshne, hchain, hlen, hcarrier, hpair, harg, havoid⟩ :=
    exists_firstReturn_actual_radial_loop ha y H hP E hpieces b r hb hbi hboundary hzw hst hs ht hd hgap
  let L := old ++ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse
  obtain ⟨n, arcs, _, hn, hmem, hv, hclose, hinj, hnat, hends, hstart, hend⟩ :=
    exists_point_radial_closed_list_slots_with_source_ends L hchain hlen hpair
  have hLne : L ≠ [] := List.length_pos_iff.mp (by omega)
  have hnewne : ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse ≠ [] := by
    intro he
    apply hfreshne
    exact List.map_eq_nil_iff.mp
      (List.map_eq_nil_iff.mp (List.reverse_eq_nil_iff.mp he))
  have hfirst : arcs 0 ∈ old := by
    rw [(hends hLne).1]
    change (old ++ _).head _ ∈ old
    rw [List.head_append_left hold.nonempty]
    exact List.head_mem hold.nonempty
  have hlast : arcs n ∈ ((fresh.map PointRadialC1ArcPiece.toPlane).map PointRadialC1PlaneArc.reverse).reverse := by
    rw [(hends hLne).2]
    change (old ++ _).getLast _ ∈ _
    rw [List.getLast_append_right hnewne]
    exact List.getLast_mem hnewne
  have hlastsource : ∃ e ∈ fresh, arcs n = e.toPlane.reverse := by
    obtain ⟨e₁, he₁, heq⟩ := List.mem_map.mp (List.mem_reverse.mp hlast)
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he₁
    exact ⟨e₀, he₀, heq.symm⟩
  have hcarrier' : (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) =
      range (lineCapSegment r z w) ∪ range (lineCapSegment b s t) := hnat.trans hcarrier
  have hdata := exists_pointFirstReturnFiniteGBData ha y arcs n hn hv hclose hinj
    (fun k _ => harg _ (hmem k)) (fun k _ => havoid _ (hmem k))
    hU hUc hV hVc hdisj hK (by rwa [hcarrier']) (by rwa [hcarrier']) (by rwa [hcarrier'])
  exact ⟨old, fresh, hold, hfresh, n, arcs, hn, hmem, hfirst, hlastsource, hstart, hend, hcarrier', hdata⟩

end RepulsiveCoulomb
