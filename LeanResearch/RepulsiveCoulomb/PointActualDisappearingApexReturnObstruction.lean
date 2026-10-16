module

public import LeanResearch.RepulsiveCoulomb.PointSectorReturnProperActualCap
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnPhysicalDirectionLink
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnActualGBLink
public import LeanResearch.RepulsiveCoulomb.PointFirstReturnVertexBookkeeping
public import LeanResearch.RepulsiveCoulomb.PointFirstReturnOldSignedCoefficients
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexReturnBudget

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Complete actual finite-GB contradiction
from a genuine metric stopped edge and a proper broken old end. The Jordan cap,
clock order, finite radial family, vertex identities and coefficient sums are
constructed. The actual initial direction is the source-derived pi offset from
the old-end local germ. There is NO pi<=alpha(z) assumption. The original apex
is excluded from the cap carrier by the proper escaping old end through it. -/
noncomputable section
open Set Topology
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem not_actual_disappearing_apex_return_of_proper_old_end
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (E : PointGeodesicTreeEdge a y) (hEP : ∀ u, E.curve u ∈ P)
    (C : PointRetainedConeNeighborhood a y P E.start) (hC : C.Admissible)
    (hφopen : C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi)
    (ρ r : ℝ → ℂ) (hρ : Continuous ρ) (hr : Continuous r)
    (hρ0 : ρ 0 = E.start)
    (hρproper : IsClosedEmbedding (fun u : NNReal ↦ ρ (u:ℝ)))
    (hq : ∀ T∈Ici (0:ℝ),E.finish≠ρ T)
    {R ξ : ℝ} (hR : 0<R) (hξ : ξ∈Icc C.lo C.hi) (hξend : ξ=C.lo ∨ ξ=C.hi)
    (hclean : ∀ u∈Ioo (0:ℝ) R,ρ u∈C.chart.source ∧
      C.chart (ρ u)=pointRadialSectorPoint u ξ)
    (hoccupied : (1+coalescedPointExponent a y E.start/2)*
      |C.actualInitialRawAngle ha y hC E rfl hEP-ξ|=Real.pi)
    (hρfront : ∀ u ∈ Ici (0:ℝ), ρ u ∈ frontier P)
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
    {p : ℂ} {β : ℝ} (hboundary : ν p=Real.pi-β)
    (hβπ : β≤Real.pi) (hβα : β≤α p) (hzneg : ν E.start<0)
    (hpRemoved : ∃ u : ℝ,0<u ∧ ρ u=p) : False := by
  have hgapE : ∀ u : unitInterval, 0 < u.1 → u.1 < 1 → E.curve u ∉ frontier P := by
    intro u hu0 hu1
    rw [hEcurve]
    change r (0+u.1*(w-0)) ∉ frontier P
    apply hgap
    constructor
    · simpa only [sub_zero,zero_add] using mul_pos hu0 hw
    · simp only [sub_zero,zero_add]
      nlinarith [hw]
  obtain ⟨b,hb,hbi,hboundaryOld,s,t,hst,hs,ht,_,U,V,hU,hV,hUc,hVc,hUV,
      hcover,hfrontU,hfrontV,hcompact,hUP,havoid,Dcap,hDwidth,hDturn⟩ :=
    exists_sectorReturn_proper_actual_cap_initial_angle ha y HP hP E hEP C hC hφopen
      ρ hρ hρ0 hρproper hq hR hξ hξend hclean hρfront hgapE hfinish
  have hcover' : U ∪ V = (range (lineCapSegment r 0 w) ∪ range (lineCapSegment b s t))ᶜ := by
    simpa only [hEcurve] using hcover
  have hfrontU' : frontier U = range (lineCapSegment r 0 w) ∪ range (lineCapSegment b s t) := by
    simpa only [hEcurve] using hfrontU
  have hfrontV' : frontier V = range (lineCapSegment r 0 w) ∪ range (lineCapSegment b s t) := by
    simpa only [hEcurve] using hfrontV
  obtain ⟨old,fresh,hold,hfresh,n,arcs,hn,hmem,_,_,_,_,hcarrier,⟨G⟩⟩ :=
    exists_firstReturn_actual_finite_GB ha y HP hP pieces hpieces b r hb hbi hboundaryOld
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
      (1+coalescedPointExponent a y ((G.oriented start).curve 0)/2)*G.angle start = ν E.start+Real.pi := by
    rw [hstartangle,hDturn,← hνC,hoccupied]
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
    rw [← hboundaryOld]
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
  have holdAvoid (i : ℕ) (hi : i≤n) (_his : i≠start) (_hif : i≠far)
      (_hiP : vertex i∈frontier P) : vertex i≠p:=by
    intro he
    obtain ⟨u,hu,hup⟩:=hpRemoved
    apply havoid u hu
    rw [hup,← he]
    have hp:=hpoint i hi
    simpa only [newArc,oldArc,← hEcurve] using hp
  exact G.not_disappearingApex_return hbudget hboundary hβπ hβα hzneg (frontier P)
    hstart hfar hne hstartturn holdAvoid hcoeff (fun i hi _ _ hiP ↦ hnew i hi hiP)


end RepulsiveCoulomb
