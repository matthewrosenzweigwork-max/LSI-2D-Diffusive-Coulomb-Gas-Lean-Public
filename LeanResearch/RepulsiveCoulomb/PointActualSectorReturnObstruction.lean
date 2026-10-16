import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualCapAngle
import LeanResearch.RepulsiveCoulomb.PointSectorReturnPhysicalDirectionLink
import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualGBLink
import LeanResearch.RepulsiveCoulomb.PointFirstReturnVertexBookkeeping
import LeanResearch.RepulsiveCoulomb.PointFirstReturnOldSignedCoefficients
import LeanResearch.RepulsiveCoulomb.PointRetainedApexFirstReturnBudget

/-!
SOURCE-ONLY, NOT COMPILED. ACTUAL metric-edge first-return obstruction with the
true signed budget and the actual initial physical direction measured from a
literal clean boundary reference edge. The Jordan cap, old clock order, finite
radial GB family, initial/far vertices, full GB angle, old signed coefficients,
and new nonpositive turns are ALL constructed. No cap, cap chart, selected turn,
positive-mass cap inequality, or no-return certificate is an input.

The original stopped minimizing edge E is related to an actual unit-speed ray
clock r; reference edge F is the literal arclength prefix of the actual clean
ray. These are geometric source/clock data, not cap conclusions. The supplied
sector source adapters still need to instantiate this endpoint.
-/
noncomputable section
open Set Topology
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem not_actual_sector_return_of_signed_budget
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (E F : PointGeodesicTreeEdge a y) (hEP : ∀ u, E.curve u ∈ P)
    (hF0 : F.start = E.start) (hFP : ∀ u, F.curve u ∈ P)
    (C : PointRetainedConeNeighborhood a y P E.start) (hC : C.Admissible)
    (hφopen : C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi)
    (ρ r : ℝ → ℂ) (hρ : Continuous ρ) (hr : Continuous r)
    (hρ0 : ρ 0 = E.start)
    (hρd : ∀ u ∈ Ici (0:ℝ), ∀ v ∈ Ici (0:ℝ),
      (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v)
    (hρfront : ∀ u ∈ Ici (0:ℝ), ρ u ∈ frontier P)
    (hFcurve : ∀ u : unitInterval, F.curve u = ρ (pointActualEdgeLength F*u.1))
    {w : ℝ} (hw : 0 < w)
    (hEcurve : E.curve = lineCapSegment r 0 w)
    (hr0 : r 0 = E.start) (hrw : r w = E.finish)
    (hrd : ∀ u ∈ Icc (0:ℝ) w, ∀ v ∈ Icc (0:ℝ) w,
      (pointSmoothConformalEDist a y (r u) (r v)).toReal = dist u v)
    (hgap : ∀ u ∈ Ioo (0:ℝ) w, r u ∉ frontier P)
    (hfinish : E.finish ∈ frontier P)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi-(1+coalescedPointExponent a y p/2)*(K.hi-K.lo))
    (hdirection : C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP ≤ α E.start) : False := by
  have hgapE : ∀ u : unitInterval, 0 < u.1 → u.1 < 1 → E.curve u ∉ frontier P := by
    intro u hu0 hu1
    rw [hEcurve]
    change r (0+u.1*(w-0)) ∉ frontier P
    apply hgap
    constructor
    · simpa only [sub_zero,zero_add] using mul_pos hu0 hw
    · simp only [sub_zero,zero_add]
      nlinarith [hw]
  obtain ⟨b,hb,hbi,hboundary,s,t,hst,hs,ht,_,U,V,hU,hV,hUc,hVc,hUV,
      hcover,hfrontU,hfrontV,hcompact,hUP,ξ,hξ,hξend,ε,hε,hclean,Dcap,hDwidth,hDturn⟩ :=
    exists_sectorReturn_actual_cap_initial_angle ha y HP hP E hEP C hC hφopen
      ρ hρ hρ0 hρd hρfront hgapE hfinish
  let θ := C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP
  have hθ0 : 0 ≤ θ := (C.actualPhysicalDirection_mem ha y hC E F rfl hF0 hEP hFP).1
  have hθ : θ = (1+coalescedPointExponent a y E.start/2)*
      |C.actualInitialRawAngle ha y hC E rfl hEP-ξ| :=
    C.actualPhysicalDirection_eq_clean_germ_offset ha y hC E F rfl hF0 hEP hFP
      ρ hFcurve hε hξ hclean
  have hcover' : U ∪ V = (range (lineCapSegment r 0 w) ∪ range (lineCapSegment b s t))ᶜ := by
    simpa only [hEcurve] using hcover
  have hfrontU' : frontier U = range (lineCapSegment r 0 w) ∪ range (lineCapSegment b s t) := by
    simpa only [hEcurve] using hfrontU
  have hfrontV' : frontier V = range (lineCapSegment r 0 w) ∪ range (lineCapSegment b s t) := by
    simpa only [hEcurve] using hfrontV
  obtain ⟨old,fresh,hold,hfresh,n,arcs,hn,hmem,_,_,_,_,hcarrier,⟨G⟩⟩ :=
    exists_firstReturn_actual_finite_GB ha y HP hP pieces hpieces b r hb hbi hboundary
      hw hst.ne (hs.trans hr0.symm) (ht.trans hrw.symm) hrd hgap
      hU hUc hV hVc hUV hcompact hcover' hfrontU' hfrontV'
  let oldArc := lineCapSegment b s t
  let newArc := lineCapSegment r 0 w
  have hOldC : Continuous oldArc := lineCapSegment_continuous hb s t
  have hNewC : Continuous newArc := lineCapSegment_continuous hr 0 w
  have hOldI : Function.Injective oldArc := lineCapSegment_injective_of_ne hbi hst.ne
  have hNewI : Function.Injective newArc := by
    change Function.Injective (lineCapSegment r 0 w)
    rw [← hEcurve]
    exact pointConformal_geodesic_injective ha y E.distinct E.curve E.geodesic
  have hOld0 : oldArc 0 = E.start := (lineCapSegment_zero b s t).trans hs
  have hOld1 : oldArc 1 = E.finish := (lineCapSegment_one b s t).trans ht
  have hNew0 : newArc 0 = E.start := (lineCapSegment_zero r 0 w).trans hr0
  have hNew1 : newArc 1 = E.finish := (lineCapSegment_one r 0 w).trans hrw
  obtain ⟨start,far,hstart,hfar,hne,hs0,hf0,hstartUnique,hfarUnique⟩ :=
    G.source_contact_vertices oldArc newArc hOldI hNewI
      (hOld0.trans hNew0.symm) (hOld1.trans hNew1.symm) old hold fresh hfresh hmem hcarrier
  have hsE : (G.oriented start).curve 0 = E.start := hs0.trans hNew0
  have hcoverN : U ∪ V = (⋃ i ≤ n, (arcs i).curve '' Icc (0:ℝ) 1)ᶜ := by
    rwa [hcarrier]
  have hfrontUN : frontier U = ⋃ i ≤ n, (arcs i).curve '' Icc (0:ℝ) 1 := by
    rwa [hcarrier]
  have hfrontVN : frontier V = ⋃ i ≤ n, (arcs i).curve '' Icc (0:ℝ) 1 := by
    rwa [hcarrier]
  have hcap : ∃ K : PointRetainedConeNeighborhood a y (closure U) ((G.oriented start).curve 0),
      (1+coalescedPointExponent a y ((G.oriented start).curve 0)/2)*(K.hi-K.lo) =
        (1+coalescedPointExponent a y E.start/2)*(Dcap.hi-Dcap.lo) := by
    rw [hsE]
    exact ⟨Dcap,rfl⟩
  obtain ⟨Kcap,hKcap⟩ := hcap
  have hstartangle := (G.physical_angle_eq_actual_cap_chart hstart Kcap hU hUc hV hVc hUV
    hcompact hcoverN hfrontUN hfrontVN).trans hKcap
  have hpfront : E.start ∈ frontier P := hρ0 ▸ hρfront 0 (show (0 : ℝ) ≤ 0 from le_rfl)
  obtain ⟨Kold,hKold⟩ := hν E.start hpfront
  have hCwidth := C.physical_width_eq Kold
  have hνC : ν E.start = Real.pi-(1+coalescedPointExponent a y E.start/2)*(C.hi-C.lo) := by
    rw [hCwidth]
    exact hKold
  have hstartturn : Real.pi-
      (1+coalescedPointExponent a y ((G.oriented start).curve 0)/2)*G.angle start = ν E.start+θ := by
    rw [hstartangle,hDturn,← hνC,← hθ]
  let vertex : ℕ → ℂ := fun i ↦ (G.oriented i).curve 0
  let turn : ℕ → ℝ := fun i ↦ Real.pi-(1+coalescedPointExponent a y (vertex i)/2)*G.angle i
  have hpoint (i : ℕ) (hi : i ≤ n) : vertex i ∈ range newArc ∪ range oldArc := by
    rw [← hcarrier,← G.carrier]
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,⟨0,by norm_num,rfl⟩⟩⟩
  have holdpoint (i : ℕ) (hi : i ≤ n) (his : i ≠ start) (hif : i ≠ far)
      (hiP : vertex i ∈ frontier P) : vertex i ∈ range oldArc ∧ vertex i ∉ range newArc := by
    apply firstReturn_other_boundary_vertex_on_old_arc hw hgap (hpoint i hi) hiP
    · intro he
      exact his (hstartUnique i hi (he.trans (hr0.trans hNew0.symm)))
    · intro he
      exact hif (hfarUnique i hi (he.trans (hrw.trans hNew1.symm)))
  have hOldFront (u : unitInterval) : oldArc u ∈ frontier P := by
    rw [← hboundary]
    exact ⟨s+u.1*(t-s),rfl⟩
  have hOldSet : range oldArc ⊆ frontier P := by rintro p ⟨u,rfl⟩; exact hOldFront u
  have hcoeff (i : ℕ) (hi : i ≤ n) (his : i ≠ start) (hif : i ≠ far)
      (hiP : vertex i ∈ frontier P) : turn i = ν (vertex i) := by
    obtain ⟨K,hK⟩ := hν (vertex i) hiP
    exact G.old_vertex_turn_eq_signed_boundary HP hP hU hUc hV hVc hUV hcompact
      hcoverN hfrontUN hfrontVN hUP (isCompact_range hNewC).isClosed
      hOldSet hfrontU' hi (holdpoint i hi his hif hiP).2 K hK
  have hnew (i : ℕ) (hi : i ≤ n) (hiP : vertex i ∉ frontier P) : turn i ≤ 0 :=
    G.new_vertex_turn_nonpos ha y old
      (fun e he u hu ↦ hold.curve_mem_boundary hOldFront he hu)
      newArc hNewI (lineCapSegment_metricOn y r hw.le hrd) fresh hmem hi hiP
  exact G.not_retainedApex_sector_return hbudget hθ0 hdirection (frontier P)
    hstart hfar hne hsE hstartturn hcoeff (fun i hi _ _ hiP ↦ hnew i hi hiP)

end RepulsiveCoulomb
