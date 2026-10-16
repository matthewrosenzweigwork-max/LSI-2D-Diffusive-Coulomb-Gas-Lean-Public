module

public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexBoundaryContinuation
public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorRelativeOpenness
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexBudget
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. If the whole upper ray remains old boundary,
actual local source disks fill P everywhere on the closed sector. Connectedness
then forces S=P. Positive residual budget rules this out using the derived
full-angle equalities and actual all-point curvature, not a prescribed exit. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Whole upper contact forces full width pi at every positive upper point
and literal local filling, including ambient singular points. -/
theorem pointDisappearingApex_upper_whole_contact_full
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (hupper : ∀ t : NNReal,σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (r : NNReal) (hr : 0<(r:ℝ))
    (C : PointRetainedConeNeighborhood a y P (σ (retainedApexUpperSource hβ.le hβπ r)))
    (hC : C.Admissible) :
    C.flatPhysicalWidth=Real.pi ∧ ∃ ε : ℝ,0<ε ∧ ∀ z,
      (pointSmoothConformalEDist a y z (σ (retainedApexUpperSource hβ.le hβπ r))).toReal≤ε →
        (z∈range σ ↔ z∈P) := by
  obtain ⟨L,hL,hLr,hLsin⟩:=retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let f : flatLinkSectorDisk Real.pi L → ℂ:=σ ∘ retainedSectorPassingHalfDisk hβ hβπ hLsin
  have hcenter : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)=
      σ (retainedApexUpperSource hβ.le hβπ r):=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le))=_
    rw [retainedSectorPassingHalfDisk_apex hβ hβπ hLsin hL.le (NNReal.coe_nonneg r)]
    rfl
  have hold : ∃ C0 : PointRetainedConeNeighborhood a y P
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      C0.Admissible ∧ C0.flatPhysicalWidth=C.flatPhysicalWidth:=by
    rw [hcenter]
    exact ⟨C,hC,rfl⟩
  obtain ⟨C0,hC0,hwidth0⟩:=hold
  have hd (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal=dist x z:=by
    dsimp only [f, Function.comp_apply]
    rw [hσ]
    exact (retainedSectorPassingHalfDisk_isometry hβ hβπ hLsin).dist_eq x z
  have hfP (x : flatLinkSectorDisk Real.pi L) : f x∈P:=hσP _
  let ε:=min L (C0.radius/2)
  have hε : 0<ε:=lt_min hL (half_pos C0.radius_pos)
  have hεL : ε≤L:=min_le_left _ _
  have hεC : ε<C0.radius:=(min_le_right _ _).trans_lt (half_lt_self C0.radius_pos)
  have hεr : ε≤r:=hεL.trans hLr.le
  have hfront0 : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ 0)∈frontier P:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P
    rw [disappearingSectorPassing_backward hβ hβπ hLsin hε.le hεL hεr]
    exact hupper _
  have hfront1 : f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ 1)∈frontier P:=by
    change σ (retainedSectorPassingHalfDisk hβ hβπ hLsin _)∈frontier P
    rw [disappearingSectorPassing_forward hβ hβπ hLsin r.2 hε.le hεL]
    exact hupper _
  obtain ⟨hwidth,hfill⟩:=pointFlatLinkDisk_fills_old_boundary_interval ha y Real.pi_pos le_rfl hL
    f hd hfP C0 hC0 hε hεL hεC hfront0 hfront1
  rw [hcenter] at hfill
  refine ⟨hwidth0.symm.trans hwidth,ε,hε,?_⟩
  intro z hz
  exact (pointRetainedSectorPassingHalfDisk_germ y hβ hβπ hLsin r.2 σ hσ
    (hz.trans hεL)).trans (hfill z hz)

/-- Entire old-ray agreement forces equality of the ACTUAL closed subsets.
The proof is relative clopenness, with actual fullness at the apex and every
positive upper point; source interior and bottom fullness are reused. -/
theorem pointDisappearingApex_whole_contact_eq_region
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hconn : IsPreconnected P) (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (hupper : ∀ t : NNReal,σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P)
    (hOld : ∀ p∈frontier P,∃ C : PointRetainedConeNeighborhood a y P p,C.Admissible)
    (hregular : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P ∧ coalescedPointExponent a y (σ x)=0)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β) : range σ=P := by
  let S:=range σ
  let T:=range (fun t : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ t))
  let V : Set P:={x | x.1∈S}
  have hclosed : IsClosed S:=(pointRetainedSector_closed_proper ha y hβ hβπ σ hσ).1.isClosed_range
  have hVclosed : IsClosed V:=hclosed.preimage continuous_subtype_val
  have hWopen:=pointRetainedSector_without_free_ray_relative_open ha y hβ hβπ σ hσ
    hσP hbottom hOld hregular
  have hVopen : IsOpen V:=by
    have hopen : @IsOpen P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace V:=by
      letI : MetricSpace P:=pointRegionMetricSpace ha y P
      letI : PseudoMetricSpace P:=(pointRegionMetricSpace ha y P).toPseudoMetricSpace
      letI : PseudoEMetricSpace P:=(pointRegionMetricSpace ha y P).toPseudoEMetricSpace
      letI : TopologicalSpace P:=(pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      have hWm : IsOpen {x : P | x.1∈S\T}:=by
        change @IsOpen P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
          {x : P | x.1 ∈ S \ T}
        rw [pointRegionMetricSpace_topology ha y P]
        exact hWopen
      apply isOpen_iff_mem_nhds.mpr
      intro q hq
      by_cases hqT : q.1∈T
      · obtain ⟨r,hrq⟩:=hqT
        change σ (retainedApexUpperSource hβ.le hβπ r) = q.1 at hrq
        have hfill : ∃ ε : ℝ,0<ε ∧ ∀ z,
            (pointSmoothConformalEDist a y z q.1).toReal≤ε → (z∈S ↔ z∈P):=by
          by_cases hr0 : r=0
          · have hqp : q.1=σ (flatLinkSectorApex hβ.le):=by
              rw [hr0] at hrq
              have hzero : retainedApexUpperSource hβ.le hβπ 0=flatLinkSectorApex hβ.le:=
                Subtype.ext (sectorPolar_zero β)
              rw [hzero] at hrq
              exact hrq.symm
            rw [hqp]
            exact pointDisappearingApex_sector_locally_full ha y hβ hβπ σ hσ hσP hbottom C hC hfull
          · have hr : 0<(r:ℝ):=lt_of_le_of_ne r.2 (fun he ↦ hr0 (Subtype.ext he.symm))
            obtain ⟨D,hD⟩:=hOld _ (hupper r)
            have hout:=(pointDisappearingApex_upper_whole_contact_full ha y hβ hβπ σ hσ hσP hupper r hr D hD).2
            rw [hrq] at hout
            exact hout
        obtain ⟨ε,hε,hfill⟩:=hfill
        apply Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hε))
        intro w hw
        exact (hfill w.1 hw.le).mpr w.2
      · exact Filter.mem_of_superset (hWm.mem_nhds ⟨hq,hqT⟩) (fun w hw ↦ hw.1)
    rwa [pointRegionMetricSpace_topology ha y P] at hopen
  letI : PreconnectedSpace P:=Subtype.preconnectedSpace hconn
  have hVne : V.Nonempty:=⟨⟨σ (flatLinkSectorApex hβ.le),hσP _⟩,mem_range_self _⟩
  have hV : V=univ:=(show IsClopen V from ⟨hVclosed,hVopen⟩).eq_univ hVne
  apply Subset.antisymm
  · rintro x ⟨q,rfl⟩
    exact hσP q
  · intro x hx
    have hm : (⟨x,hx⟩:P)∈V:=by rw [hV]; trivial
    exact hm

/-- Positive residual budget produces an actual finite upper-ray noncontact.
The whole-contact alternative is ruled out by literal S=P and its true
all-point curvature coefficients, not by a residual-region certificate. -/
theorem pointDisappearingApex_exists_upper_noncontact
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hconn : IsPreconnected P) (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (hregular : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P ∧ coalescedPointExponent a y (σ x)=0)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hνC : ν (σ (flatLinkSectorApex hβ.le))=Real.pi-C.flatPhysicalWidth)
    (hβα : β≤α (σ (flatLinkSectorApex hβ.le)))
    (hremaining : 0<pointSignedBudgetMass ν α-β)
    (hνoff : ∀ x,x∉P → ν x=0)
    (hνint : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνboundary : ∀ x∈frontier P,∃ D : PointRetainedConeNeighborhood a y P x,
      ν x=Real.pi-D.flatPhysicalWidth ∧ D.Admissible)
    (hbottomclean : ∀ t : NNReal,0<(t:ℝ) → ν (σ (retainedApexBottomSource hβ.le hβπ t))=0) :
    ∃ t : NNReal,σ (retainedApexUpperSource hβ.le hβπ t)∉frontier P := by
  classical
  by_contra hnot
  push_neg at hnot
  let p:=σ (flatLinkSectorApex hβ.le)
  have hboundary : ν p=Real.pi-β:=by simpa only [hfull] using hνC
  obtain ⟨_,hνp,_,_,_,hαpart⟩:=hbudget.disappearingApex_equalities p hboundary hβπ hβα
  have hOld : ∀ x∈frontier P,∃ D : PointRetainedConeNeighborhood a y P x,D.Admissible:=by
    intro x hx
    obtain ⟨D,_,hD⟩:=hνboundary x hx
    exact ⟨D,hD⟩
  have hSP:=pointDisappearingApex_whole_contact_eq_region ha y hβ hβπ σ hσ hconn hσP
    hbottom hnot hOld hregular C hC hfull
  have hnonneg : ∀ x,0≤ν x:=by
    intro x
    by_cases hxP : x∈P
    · obtain ⟨q,hqx⟩:=hSP.symm ▸ hxP
      subst x
      by_cases hq0 : q.1=0
      · have hqp : q=flatLinkSectorApex hβ.le:=Subtype.ext hq0
        simpa only [hqp] using hνp
      have hqpos : 0<‖q.1‖:=norm_pos_iff.mpr hq0
      by_cases harg0 : Complex.arg q.1=0
      · have hqb : retainedApexBottomSource hβ.le hβπ ⟨‖q.1‖,norm_nonneg _⟩=q:=by
          apply Subtype.ext
          change sectorPolar ‖q.1‖ 0=q.1
          rw [← harg0,sectorPolar_norm_arg]
        have hz:=hbottomclean ⟨‖q.1‖,norm_nonneg _⟩ hqpos
        rw [hqb] at hz
        exact hz.ge
      by_cases hargβ : Complex.arg q.1=β
      · let r : NNReal:=⟨‖q.1‖,norm_nonneg _⟩
        have hqt : retainedApexUpperSource hβ.le hβπ r=q:=by
          apply Subtype.ext
          change sectorPolar ‖q.1‖ β=q.1
          exact (congrArg (sectorPolar ‖q.1‖) hargβ).symm.trans (sectorPolar_norm_arg q.1)
        obtain ⟨D,hνD,hD⟩:=hνboundary _ (hnot r)
        have hw:=(pointDisappearingApex_upper_whole_contact_full ha y hβ hβπ σ hσ
          hσP hnot r hqpos D hD).1
        rw [hw,sub_self,hqt] at hνD
        exact hνD.ge
      · obtain ⟨hqI,hqκ⟩:=hregular q hqpos (lt_of_le_of_ne q.2.1 (Ne.symm harg0))
          (lt_of_le_of_ne q.2.2 hargβ)
        rw [hνint _ hqI,hqκ,mul_zero]
    · rw [hνoff x hxP]
  have hpart0 : pointSignedNegativePart ν=0:=by
    ext x
    simp only [pointSignedNegativePart_apply,Finsupp.zero_apply]
    exact max_eq_right (neg_nonpos.mpr (hnonneg x))
  have hαzero : retainedApexBudget α p β=0:=hαpart.trans hpart0
  have hmass:=(retainedApex_mass_changes ν α p β).2
  have hzeroMass : pointSignedBudgetMass (retainedApexCurvature ν p β)
      (retainedApexBudget α p β)=0:=by
    rw [hαzero,pointSignedBudgetMass_eq_support_sum]
    simp
  rw [hzeroMass] at hmass
  linarith

end RepulsiveCoulomb
