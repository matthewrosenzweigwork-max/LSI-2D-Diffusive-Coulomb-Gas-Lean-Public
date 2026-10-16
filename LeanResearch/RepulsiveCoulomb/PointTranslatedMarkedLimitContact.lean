module

public import LeanResearch.RepulsiveCoulomb.PointMarkedParallelEdgeInterior
public import LeanResearch.RepulsiveCoulomb.PointTranslatedContactAngle
public import LeanResearch.RepulsiveCoulomb.PointTranslatedBackwardEnd
public import LeanResearch.RepulsiveCoulomb.PointTranslatedRowClock

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Exact old-boundary contact for the attained marked
limit once strict residual-angle positivity has been separately established.
Every cap, first return, backward end, direction, stopped metric edge and signed
attachment charge is constructed. The assumption of strict remaining width is
explicit in this intermediate lemma; the original-data endpoint must discharge
it using the separate no-clean/extreme-end zero-angle exclusion. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem translatedStripEdge_isometry {v : ℂ} (hv : ‖v‖=1) {b : ℝ} :
    Isometry (@translatedStripEdge v b) := by
  apply Isometry.of_dist_eq
  intro u w
  change dist (flatShearedPoint v 0 u.1) (flatShearedPoint v 0 w.1)=dist u.1 w.1
  simp only [flatShearedPoint,Complex.ofReal_zero,zero_add,dist_eq_norm,Real.dist_eq]
  rw [← sub_mul,norm_mul,hv,mul_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

namespace PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m→ℝ} {y : Fin m→ℂ} {ha : ∀ j,0≤a j}
  {P : Set ℂ} {ν α : ℂ→₀ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  (K : D.FiniteWidthLimit)

theorem marked_top_positive_interior_of_positive_residual
    (C : PointRetainedConeNeighborhood a y P
      (K.map (translatedStripTop K.positive.le 0)).1) (hC : C.Admissible)
    (hremain : Real.pi-D.angle<C.flatPhysicalWidth) :
    ∀ t : NNReal,0<t→(K.map (translatedStripTop K.positive.le t)).1∈interior P := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  intro t ht
  let b := sSup D.regularWidths
  let R := t.1+1
  have hR : 0<R := by dsimp [R]; linarith [t.2]
  have htR : t.1∈Icc (0:ℝ) R := ⟨t.2,by dsimp [R];linarith⟩
  have hrect : flatShearedRectangle (conePhase D.angle) R b⊆flatShearedStrip (conePhase D.angle) b := by
    rintro z ⟨r,hr,u,hu,rfl⟩
    exact ⟨r,hr.1,u,hu,rfl⟩
  let f := K.map∘Set.inclusion hrect
  have hf : Isometry f := K.metric.comp (show Isometry (Set.inclusion hrect) from fun _ _ ↦ rfl)
  let edge : Icc (0:ℝ) b→P := K.map∘translatedStripEdge
  have hedge : Isometry edge := K.metric.comp (translatedStripEdge_isometry (conePhase_norm D.angle))
  have hbottom (r : Icc (0:ℝ) R) : f (shearedBottomPoint K.positive.le r)=D.ray ⟨r.1,r.2.1⟩ := by
    change K.map (translatedStripBottom K.positive.le ⟨r.1,r.2.1⟩)=_
    exact K.bottom _
  have hold (u : Icc (0:ℝ) b) : f (shearedCompactEdgePoint hR.le u)=edge u := rfl
  obtain ⟨δ,hδ,hδ0,hδb,hδrange,hδfront,hδback,hδavoid⟩ :=
    point_exists_translated_backward_end ha y D.angle_pos D.angle_lt_pi hR K.positive
      D.ray D.ray_metric D.ray_frontier edge hedge K.edge_frontier f hf hbottom hold
  obtain ⟨E,hE0,hE1,hEL,hEP,r,hrc,hr0,hrd,hEclock,hrow⟩ :=
    point_exists_translated_row_clock ha y hR f hf ⟨b,K.positive.le,le_rfl⟩
  let backward : ℝ→ℂ := δ∘Real.toNNReal
  have hbc : Continuous backward := hδ.continuous.comp continuous_real_toNNReal
  have hb0 : backward 0=E.start := by
    simpa only [backward,Function.comp_apply,Real.toNNReal_zero,edge,f,Function.comp_apply] using
      hδ0.trans hE0.symm
  have hbproper : IsClosedEmbedding (fun u : NNReal ↦ backward (u:ℝ)) := by
    simpa only [backward,Function.comp_apply,Real.toNNReal_coe] using hδ
  have hbfront : ∀ u∈Ici (0:ℝ),backward u∈frontier P := fun u _ ↦ hδfront _
  let CE : PointRetainedConeNeighborhood a y P E.start := hE0.symm ▸ C
  have htransport {p q : ℂ} (he : p=q)
      (A : PointRetainedConeNeighborhood a y P p) (hA : A.Admissible) :
      (he ▸ A).Admissible ∧ (he ▸ A).flatPhysicalWidth=A.flatPhysicalWidth := by
    cases he
    exact ⟨hA,rfl⟩
  have hCE : CE.Admissible := (htransport hE0.symm C hC).1
  have hremainE : Real.pi-D.angle<CE.flatPhysicalWidth :=
    hremain.trans_eq (htransport hE0.symm C hC).2.symm
  let β := Real.pi-D.angle
  have hβ : 0<β := sub_pos.mpr D.angle_lt_pi
  have hβπ : β≤Real.pi := by dsimp [β];linarith [D.angle_pos]
  obtain ⟨hL₀,hL₀b⟩ := translatedStripCorner_radius D.angle_pos D.angle_lt_pi K.positive
  let L := min (b*Real.sin D.angle/2) (R/2)
  have hL : 0<L := lt_min hL₀ (half_pos hR)
  have hLR : L<R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hLb : L≤b*Real.sin D.angle := (min_le_left _ _).trans hL₀b
  have hLb' : L≤b := hLb.trans (mul_le_of_le_one_right K.positive.le (Real.sin_le_one D.angle))
  let J := translatedStripCornerSource D.angle_pos D.angle_lt_pi hLb
  let g : flatLinkSectorDisk β L→ℂ := fun z ↦ (K.map (J z)).1
  have hg : ∀ x z,(pointSmoothConformalEDist a y (g x) (g z)).toReal=dist x z := by
    intro x z
    have hm := @Isometry.dist_eq _ P _ M.toPseudoMetricSpace K.map K.metric (J x) (J z)
    change (pointSmoothConformalEDist a y (g x) (g z)).toReal=dist (J x) (J z) at hm
    exact hm.trans ((translatedStripCornerSource_isometry D.angle_pos D.angle_lt_pi hLb).dist_eq x z)
  have hcenter : g (flatLinkSectorDiskApex hβ.le hL.le)=E.start := by
    have he : J (flatLinkSectorDiskApex hβ.le hL.le)=translatedStripTop K.positive.le 0 := by
      apply Subtype.ext
      exact translatedStripCornerRigid_zero D.angle b
    change (K.map (J _)).1=E.start
    rw [he]
    exact hE0.symm
  have hback : ∀ u : ℝ,∀ hu : 0≤u,∀ huL : u≤L,
      g (flatLinkSectorDiskPoint hβ.le hβπ u ⟨hu,huL⟩ 0)=backward u := by
    intro u hu huL
    have hub : u≤b := huL.trans hLb'
    let w : Icc (0:ℝ) b := ⟨b-u,sub_nonneg.mpr hub,sub_le_self _ hu⟩
    have he : J (flatLinkSectorDiskPoint hβ.le hβπ u ⟨hu,huL⟩ 0)=translatedStripEdge w := by
      apply Subtype.ext
      change translatedStripCornerRigid D.angle b (sectorPolar u (β*(0:unitInterval).1))=
        flatShearedPoint (conePhase D.angle) 0 (b-u)
      simp only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero]
      exact translatedStripCornerRigid_edge_zero D.angle b u
    have hbval : backward u=δ ⟨u,hu⟩ := by
      apply congrArg δ
      exact Real.toNNReal_of_nonneg hu
    rw [hbval,hδback ⟨u,hu⟩ hub]
    change (K.map (J _)).1=(K.map (translatedStripEdge w)).1
    rw [he]
  have hout : ∀ u : ℝ,∀ hu : 0≤u,∀ huL : u≤L,
      g (flatLinkSectorDiskPoint hβ.le hβπ u ⟨hu,huL⟩ 1)=r u := by
    intro u hu huL
    have huR : u∈Icc (0:ℝ) R := ⟨hu,(huL.trans hLR.le)⟩
    have he : J (flatLinkSectorDiskPoint hβ.le hβπ u ⟨hu,huL⟩ 1)=
        translatedStripTop K.positive.le ⟨u,hu⟩ := by
      apply Subtype.ext
      change translatedStripCornerRigid D.angle b (sectorPolar u (β*(1:unitInterval).1))=
        flatShearedPoint (conePhase D.angle) u b
      simp only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one]
      exact translatedStripCornerRigid_edge_aperture D.angle b u
    change (K.map (J _)).1=r u
    rw [he]
    exact (hrow ⟨u,huR⟩).symm
  have havoid : ∀ u∈Ioc (0:ℝ) (pointActualEdgeLength E),
      ∀ v∈Ici (0:ℝ),r u≠backward v := by
    intro u hu v hv he
    have huR : u∈Icc (0:ℝ) R := ⟨hu.1.le,hEL ▸ hu.2⟩
    apply hδavoid ⟨u,huR⟩ hu.1
    exact ⟨v.toNNReal,he.symm.trans (hrow ⟨u,huR⟩)⟩
  let A := min L CE.radius/2
  have hA : 0<A := half_pos (lt_min hL CE.radius_pos)
  have hAL : A≤L := (half_le_self (le_of_lt (lt_min hL CE.radius_pos))).trans (min_le_left _ _)
  have hAC : A<CE.radius := (half_lt_self (lt_min hL CE.radius_pos)).trans_le (min_le_right _ _)
  have hpRemoved : ∃ u : ℝ,0<u ∧ backward u=(D.ray 0).1 := by
    refine ⟨b,K.positive,?_⟩
    change δ (sSup D.regularWidths).toNNReal=(D.ray 0).1
    rw [Real.toNNReal_of_nonneg K.positive.le]
    exact hδb
  have hint := point_actual_marked_parallel_edge_positive_mem_interior ha y D.ambient D.region_eq
    D.pieces D.boundary_cover hL hβ hβπ g hg (fun z ↦ (K.map (J z)).2)
    E hEP hcenter CE hCE hremainE backward r hbc hrc hb0 hbproper hback hout hA hAL hAC
    hbfront hr0 hrd hEclock havoid D.budget D.boundary_formula D.apex_coefficient hpRemoved
  let u : unitInterval := ⟨t.1/R,div_nonneg t.2 hR.le,(div_le_one hR).mpr htR.2⟩
  have hu : 0<u.1 := div_pos ht hR
  have htime : pointActualEdgeLength E*u.1=t.1 := by rw [hEL];exact mul_div_cancel₀ _ hR.ne'
  have he : E.curve u=(K.map (translatedStripTop K.positive.le t)).1 := by
    rw [hEclock u,htime]
    exact hrow ⟨t.1,htR⟩
  exact he ▸ hint u hu

/-- Old-boundary contact is exactly bottom plus compact edge, even when the
new free top carries old interior cone marks. -/
theorem exact_old_contact_of_positive_residual
    (C : PointRetainedConeNeighborhood a y P
      (K.map (translatedStripTop K.positive.le 0)).1) (hC : C.Admissible)
    (hremain : Real.pi-D.angle<C.flatPhysicalWidth) :
    range (fun q ↦ (K.map q).1)∩frontier P=
      range (fun r ↦ (K.map (translatedStripBottom K.positive.le r)).1) ∪
      range (fun u ↦ (K.map (translatedStripEdge u)).1) := by
  ext x
  constructor
  · rintro ⟨⟨q,rfl⟩,hqfront⟩
    obtain ⟨r,hr,u,hu,hq⟩ := q.2
    by_cases hr0 : r=0
    · right
      refine ⟨⟨u,hu⟩,?_⟩
      apply congrArg (fun q ↦ (K.map q).1)
      apply Subtype.ext
      change flatShearedPoint (conePhase D.angle) 0 u=q.1
      simpa only [hr0] using hq.symm
    · by_cases hu0 : u=0
      · left
        refine ⟨⟨r,hr⟩,?_⟩
        apply congrArg (fun q ↦ (K.map q).1)
        apply Subtype.ext
        change flatShearedPoint (conePhase D.angle) r 0=q.1
        simpa only [hu0] using hq.symm
      · have hrpos : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
        have hupos : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hint : (K.map q).1∈interior P := by
          by_cases hub : u<sSup D.regularWidths
          · have he : q=⟨flatShearedPoint (conePhase D.angle) r u,r,hr,u,hu,rfl⟩ := Subtype.ext hq
            rw [he]
            exact K.below_positive_interior ⟨r,hr⟩ hrpos ⟨u,hu⟩ hupos hub
          · have heq : u=sSup D.regularWidths := le_antisymm hu.2 (le_of_not_gt hub)
            have he : q=translatedStripTop K.positive.le ⟨r,hr⟩ :=
              Subtype.ext (by
                change q.1=flatShearedPoint (conePhase D.angle) r (sSup D.regularWidths)
                simpa only [heq] using hq)
            rw [he]
            exact K.marked_top_positive_interior_of_positive_residual C hC hremain ⟨r,hr⟩ hrpos
        exact (hqfront.2 hint).elim
  · rintro (⟨r,rfl⟩|⟨u,rfl⟩)
    · exact ⟨mem_range_self _,by
        change (K.map (translatedStripBottom K.positive.le r)).1∈frontier P
        rw [K.bottom]
        exact D.ray_frontier r⟩
    · exact ⟨mem_range_self _,K.edge_frontier u⟩

end PointTranslatedRegularData.FiniteWidthLimit
end RepulsiveCoulomb
