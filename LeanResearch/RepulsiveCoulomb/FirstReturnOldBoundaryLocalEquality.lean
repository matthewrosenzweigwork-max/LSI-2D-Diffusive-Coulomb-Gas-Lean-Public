import LeanResearch.RepulsiveCoulomb.PlanarFirstReturnJordanCaps
import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

/-! Source-only draft. A bounded first-return cap agrees with the literal old
closed halfplane at every old-arc point away from the stopped ray. This is a
set-germ conclusion, not a selected-angle assumption. No geodesic, curvature,
or Gauss--Bonnet hypothesis is needed for this topological step. -/
noncomputable section
open Set Topology Metric
namespace RepulsiveCoulomb

/-- The clopen argument in the actual retained interior. Frontier containment,
cap containment and a frontier point force the whole connected local retained
interior into the cap. Local regular-closedness then includes both old rays. -/
theorem cap_eq_old_region_on_connected_neighborhood
    {X : Type*} [TopologicalSpace X] {P U W : Set X} {p : X}
    (hU : IsOpen U) (hUP : closure U ⊆ P)
    (hW : IsOpen W) (hpW : p ∈ W) (hpU : p ∈ frontier U)
    (hconn : IsPreconnected (W ∩ interior P))
    (hfront : W ∩ frontier U ⊆ frontier P)
    (hregular : P ⊆ closure (interior P)) :
    W ∩ U = W ∩ interior P ∧ W ∩ closure U = W ∩ P := by
  have hUint : U ⊆ interior P :=
    hU.subset_interior_iff.mpr (subset_closure.trans hUP)
  obtain ⟨q, hqW, hqU⟩ := mem_closure_iff.mp
    (frontier_subset_closure hpU) W hW hpW
  have hseed : ((W ∩ interior P) ∩ U).Nonempty :=
    ⟨q, ⟨hqW, hUint hqU⟩, hqU⟩
  have hlocal : W ∩ interior P ⊆ U := by
    apply hconn.subset_of_closure_inter_subset hU hseed
    intro x hx
    by_contra hxU
    have hxF : x ∈ frontier U := ⟨hx.1, by simpa only [hU.interior_eq] using hxU⟩
    exact (hfront ⟨hx.2.1, hxF⟩).2 hx.2.2
  constructor
  · exact Subset.antisymm
      (fun _ hx => ⟨hx.1, hUint hx.2⟩)
      (fun _ hx => ⟨hx.1, hlocal hx⟩)
  · apply Subset.antisymm
    · exact fun _ hx => ⟨hx.1, hUP hx.2⟩
    · intro x hx
      exact ⟨hx.1, (closure_mono hlocal) (hW.inter_closure ⟨hx.1, hregular hx.2⟩)⟩

/-- The actual halfplane straightening supplies regular-closedness and small
neighborhoods with connected retained interior. These are ordinary local
halfplane topology facts; no cap sector is among the hypotheses. -/
theorem straightened_halfplane_local_connected_interior
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    {p : ℂ} {O : Set ℂ} (hO : IsOpen O) (hpO : p ∈ O) :
    P ⊆ closure (interior P) ∧
      ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧
        IsPreconnected (W ∩ interior P) := by
  have hint : interior P = H ⁻¹' planarOpenUpperHalfplane := by
    rw [hP, ← H.preimage_interior]
    exact congrArg (fun S : Set ℂ => H ⁻¹' S) (Complex.interior_setOfPred_le_im 0)
  have hreg : P = closure (interior P) := by
    rw [hint, ← H.preimage_closure, planar_halfplane_partition.2.2.2.2.2.2.1, ← hP]
  have hpre : IsOpen (H.symm ⁻¹' O) := hO.preimage H.symm.continuous
  have hp : H p ∈ H.symm ⁻¹' O := by simpa only [mem_preimage, H.symm_apply_apply] using hpO
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds hp)
  let W := H ⁻¹' ball (H p) ε
  refine ⟨hreg.subset, W, isOpen_ball.preimage H.continuous, ?_, ?_, ?_⟩
  · exact mem_ball_self hε
  · intro z hz
    have h := hball hz
    simpa only [mem_preimage, H.symm_apply_apply] using h
  · have hconv : Convex ℝ (ball (H p) ε ∩ planarOpenUpperHalfplane) :=
      (convex_ball (H p) ε).inter
        (convex_halfSpace_gt (.mk Complex.add_im Complex.smul_im) (0 : ℝ))
    rw [hint]
    change IsPreconnected (H ⁻¹' (ball (H p) ε ∩ planarOpenUpperHalfplane))
    exact H.isPreconnected_preimage.mpr hconv.isPreconnected

/-- Away from the stopped-ray carrier `K`, an actual cap whose remaining
frontier is contained in the old boundary has the SAME closed and open local
side as `P`. A compact stopped ray makes `K` closed automatically. The old
boundary may have any positive full retained angle, including a reflex one. -/
theorem firstReturn_cap_old_boundary_local_equality
    {P U K A : Set ℂ} (H : ℂ ≃ₜ ℂ)
    (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hU : IsOpen U) (hUP : closure U ⊆ P)
    (hK : IsClosed K) (hA : A ⊆ frontier P)
    (hboundary : frontier U = K ∪ A)
    {p : ℂ} (hp : p ∈ frontier U) (hpK : p ∉ K) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧ W ⊆ Kᶜ ∧
      W ∩ U = W ∩ interior P ∧ W ∩ closure U = W ∩ P := by
  obtain ⟨hregular, W, hW, hpW, hWK, hconn⟩ :=
    straightened_halfplane_local_connected_interior H hP hK.isOpen_compl hpK
  have hfront : W ∩ frontier U ⊆ frontier P := by
    intro z hz
    rw [hboundary] at hz
    exact hA (hz.2.resolve_left (hWK hz.1))
  obtain ⟨hopen, hclosed⟩ := cap_eq_old_region_on_connected_neighborhood
    hU hUP hW hpW hp hconn hfront hregular
  exact ⟨W, hW, hpW, hWK, hopen, hclosed⟩

/-- Direct specialization to the literal two carriers produced by firstReturn5.
The stopped interval is compact, and every old-arc image point is on the actual
old frontier. No selected local interval or equality of angles is assumed. -/
theorem firstReturn_actual_cap_old_arc_germ
    {P U : Set ℂ} (H : ℂ ≃ₜ ℂ)
    (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (b r : ℝ → ℂ) (hr : Continuous r)
    (hboundaryP : range b = frontier P)
    {z w s t : ℝ}
    (hU : IsOpen U) (hUP : closure U ⊆ P)
    (hboundaryU : frontier U =
      range (lineCapSegment r z w) ∪ range (lineCapSegment b s t))
    {p : ℂ} (hp : p ∈ range (lineCapSegment b s t))
    (hpnew : p ∉ range (lineCapSegment r z w)) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      W ∩ U = W ∩ interior P ∧ W ∩ closure U = W ∩ P := by
  have hK : IsClosed (range (lineCapSegment r z w)) :=
    (isCompact_range (lineCapSegment_continuous hr z w)).isClosed
  have hA : range (lineCapSegment b s t) ⊆ frontier P := by
    rintro q ⟨u, rfl⟩
    rw [← hboundaryP]
    exact ⟨s + u.1 * (t - s), rfl⟩
  have hpF : p ∈ frontier U := by rw [hboundaryU]; exact Or.inr hp
  obtain ⟨W, hW, hpW, _, hopen, hclosed⟩ :=
    firstReturn_cap_old_boundary_local_equality H hP hU hUP hK hA hboundaryU hpF hpnew
  exact ⟨W, hW, hpW, hopen, hclosed⟩


/-- A genuine old retained cone chart is transported unchanged to the cap
near every old-arc point away from the new ray. This keeps the complete
ordered interval [C.lo,C.hi]; even its reflex portion is retained. -/
theorem firstReturn_actual_cap_retained_interval
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P U : Set ℂ} (H : ℂ ≃ₜ ℂ)
    (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (b r : ℝ → ℂ) (hr : Continuous r)
    (hboundaryP : range b = frontier P)
    {z w s t : ℝ}
    (hU : IsOpen U) (hUP : closure U ⊆ P)
    (hboundaryU : frontier U =
      range (lineCapSegment r z w) ∪ range (lineCapSegment b s t))
    {p : ℂ} (hp : p ∈ range (lineCapSegment b s t))
    (hpnew : p ∉ range (lineCapSegment r z w))
    (C : PointRetainedConeNeighborhood a y P p) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, (pointSmoothConformalEDist a y x p).toReal ≤ C.radius →
        (x ∈ closure U ↔ C.chart x ∈ pointClosedRadialInterval C.radius C.lo C.hi) := by
  obtain ⟨W, hW, hpW, _, hsame⟩ := firstReturn_actual_cap_old_arc_germ
    H hP b r hr hboundaryP hU hUP hboundaryU hp hpnew
  refine ⟨W, hW, hpW, ?_⟩
  intro x hx hxR
  have hmem : x ∈ closure U ↔ x ∈ P := by
    have he := Set.ext_iff.mp hsame x
    simpa only [mem_inter_iff, hx, true_and] using he
  exact hmem.trans (C.retained x hxR)

end RepulsiveCoulomb
