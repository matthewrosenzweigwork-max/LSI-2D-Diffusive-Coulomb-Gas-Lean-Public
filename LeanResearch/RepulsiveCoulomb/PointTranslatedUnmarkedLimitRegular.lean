import LeanResearch.RepulsiveCoulomb.PointTranslatedFiniteWidthLimit
import LeanResearch.RepulsiveCoulomb.PointUnmarkedRayBoundaryPropagation
import LeanResearch.RepulsiveCoulomb.PointTranslatedStripOldEdgeFullness

/-! SOURCE-ONLY, UNCOMPILED. If the actual attained finite limit has no new
marked point, it is an actual regular stage. Boundary contact of its unmarked
free ray is clopen by genuine retained-flat charts. If every top point were
old boundary, the two old-frontier germs at its origin would force physical
width pi-lambda there, contradicting its unmarked physical width pi. Thus the
entire positive-time top is interior. No return gap or certificate is supplied.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j,0≤a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  (K : D.FiniteWidthLimit)

theorem top_ne_apex (r : NNReal) :
    (K.map (translatedStripTop K.positive.le r)).1 ≠ (D.ray 0).1 := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  intro he
  have hbot := congrArg Subtype.val (K.bottom 0)
  have heq := K.metric.injective (Subtype.ext (he.trans hbot.symm))
  have hcoord := flatShearedPoint_coordinates_eq D.direction_im_ne_zero (congrArg Subtype.val heq)
  exact K.positive.ne' hcoord.2

theorem top_origin_frontier :
    (K.map (translatedStripTop K.positive.le 0)).1∈frontier P :=
  K.edge_frontier ⟨sSup D.regularWidths,K.positive.le,le_rfl⟩

/-- The top has zero signed coefficient at every point when it has no new
marked point; in particular every possible old-boundary contact is flat. -/
theorem top_coeff_zero
    (hclean : ∀ q,(K.map q).1∉(↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1})
    (r : NNReal) : ν (K.map (translatedStripTop K.positive.le r)).1=0 :=
  (pointSigned_eq_zero_off_marked (fun hm ↦ hclean _ ⟨hm,K.top_ne_apex r⟩)).1

theorem unmarked_top_positive_interior
    (hclean : ∀ q,(K.map q).1∉(↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1}) :
    ∀ r : NNReal,0<r→(K.map (translatedStripTop K.positive.le r)).1∈interior P := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let ρ : NNReal→P := K.map∘translatedStripTop K.positive.le
  have hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ :=
    K.metric.comp (translatedStripTop_isometry K.positive.le)
  have hflat : ∀ r : NNReal,0<r→(ρ r).1∈frontier P→
      ∃ C : PointRetainedConeNeighborhood a y P (ρ r).1,C.flatPhysicalWidth=Real.pi := by
    intro r hr hf
    obtain ⟨C,_,he⟩ := D.boundary_coeff (ρ r).1 hf
    refine ⟨C,?_⟩
    have hz := K.top_coeff_zero hclean r
    change ν (ρ r).1=0 at hz
    linarith
  rcases pointMetricRay_regular_boundary_contact_all_or_none ha y ρ hρ hflat with hnone|hall
  · intro r hr
    by_contra hn
    exact hnone r hr ⟨subset_closure (ρ r).2,hn⟩
  · have htop : ∀ r : NNReal,(ρ r).1∈frontier P := by
      intro r
      by_cases hr : r=0
      · simpa only [hr,ρ,Function.comp_apply] using K.top_origin_frontier
      · exact hall r (lt_of_le_of_ne (show (0 : NNReal) ≤ r from zero_le) (Ne.symm hr))
    obtain ⟨C,hC,hνC⟩ := D.boundary_coeff _ K.top_origin_frontier
    have hCπ : C.flatPhysicalWidth=Real.pi := by
      have hz := K.top_coeff_zero hclean 0
      linarith
    let β := Real.pi-D.angle
    let L := sSup D.regularWidths*Real.sin D.angle/2
    have hβ : 0<β := sub_pos.mpr D.angle_lt_pi
    have hβπ : β≤Real.pi := by dsimp [β]; linarith [D.angle_pos]
    obtain ⟨hL,hLbound⟩ := translatedStripCorner_radius D.angle_pos D.angle_lt_pi K.positive
    let J := translatedStripCornerSource D.angle_pos D.angle_lt_pi hLbound
    let q := translatedStripTop (v:=conePhase D.angle) K.positive.le 0
    have hJ0 : J (flatLinkSectorDiskApex hβ.le hL.le)=q := by
      apply Subtype.ext
      exact translatedStripCornerRigid_zero D.angle (sSup D.regularWidths)
    have hfront : ∀ r : ℝ,∀ hr : r∈Icc (0:ℝ) L,
        (K.map (J (flatLinkSectorDiskPoint hβ.le hβπ r hr 0))).1∈frontier P ∧
        (K.map (J (flatLinkSectorDiskPoint hβ.le hβπ r hr 1))).1∈frontier P := by
      intro r hr
      have hrb : r ≤ sSup D.regularWidths := hr.2.trans (hLbound.trans
        (mul_le_of_le_one_right K.positive.le (Real.sin_le_one D.angle)))
      let u : Icc (0:ℝ) (sSup D.regularWidths) :=
        ⟨sSup D.regularWidths-r,sub_nonneg.mpr hrb,sub_le_self _ hr.1⟩
      have he0 : J (flatLinkSectorDiskPoint hβ.le hβπ r hr 0)=translatedStripEdge u := by
        apply Subtype.ext
        change translatedStripCornerRigid D.angle (sSup D.regularWidths)
          (sectorPolar r (β*(0:unitInterval).1))=flatShearedPoint (conePhase D.angle) 0 (sSup D.regularWidths-r)
        simp only [show ((0:unitInterval):ℝ)=0 from rfl,mul_zero]
        exact translatedStripCornerRigid_edge_zero D.angle (sSup D.regularWidths) r
      have he1 : J (flatLinkSectorDiskPoint hβ.le hβπ r hr 1)=
          translatedStripTop K.positive.le ⟨r,hr.1⟩ := by
        apply Subtype.ext
        change translatedStripCornerRigid D.angle (sSup D.regularWidths)
          (sectorPolar r (β*(1:unitInterval).1))=flatShearedPoint (conePhase D.angle) r (sSup D.regularWidths)
        simp only [show ((1:unitInterval):ℝ)=1 from rfl,mul_one]
        exact translatedStripCornerRigid_edge_aperture D.angle (sSup D.regularWidths) r
      exact ⟨he0.symm ▸ K.edge_frontier u,he1.symm ▸ htop ⟨r,hr.1⟩⟩
    have hwidth := (pointFlatBoundaryPatch_fullness ha y K.map
      (fun x z ↦ K.metric.dist_eq x z) hβ hβπ hL J
      (translatedStripCornerSource_isometry D.angle_pos D.angle_lt_pi hLbound) q hJ0 hfront C hC).1
    have hfalse : False := by
      dsimp [β] at hwidth
      linarith [D.angle_pos]
    exact hfalse.elim

/-- No-new-mark finite limits are genuine regular members of the already
constructed width set, with no new chart, germ or contact assumptions. -/
def toRegularStage
    (hclean : ∀ q,(K.map q).1∉(↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1}) :
    D.Stage (sSup D.regularWidths) where
  positive := K.positive
  map := K.map
  metric := K.metric
  bottom := K.bottom
  edge_frontier := K.edge_frontier
  unmarked := hclean
  positive_interior := by
    intro r hr u hu
    by_cases hub : u.1<sSup D.regularWidths
    · exact K.below_positive_interior r hr u hu hub
    · have he : u.1=sSup D.regularWidths := le_antisymm u.2.2 (le_of_not_gt hub)
      have hq : (⟨flatShearedPoint (conePhase D.angle) r.1 u.1,
          r.1,r.2,u.1,u.2,rfl⟩ : flatShearedStrip (conePhase D.angle) (sSup D.regularWidths))=
          translatedStripTop K.positive.le r :=
        Subtype.ext (congrArg (fun t : ℝ ↦ flatShearedPoint (conePhase D.angle) r.1 t) he)
      rw [hq]
      exact K.unmarked_top_positive_interior hclean r hr

end RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
