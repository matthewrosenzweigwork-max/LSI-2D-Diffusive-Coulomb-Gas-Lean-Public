import LeanResearch.RepulsiveCoulomb.PointDisappearingApexPrefixFullness
import LeanResearch.RepulsiveCoulomb.RetainedSectorSourceTopology
import Mathlib.Analysis.Convex.PathConnected

/-! SOURCE-ONLY, UNCOMPILED. Connectedness and relative openness of the
literal removed piece S minus the UPPER TAIL BASED AT z. The original apex and
compact upper prefix belong to this removed piece. These properties are
constructed from source radial contraction and actual old-chart fullness. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem disappearingSector_without_tail_connected {Y : Type*} [TopologicalSpace Y]
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi) (r : NNReal) (hr : 0<(r:ℝ))
    (σ : closedEuclideanSector β → Y) (hσ : Continuous σ) (hinj : Function.Injective σ) :
    IsConnected (range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t))) := by
  let V : Set ℂ:={q | q∈closedEuclideanSector β ∧ (Complex.arg q<β ∨ ‖q‖<(r:ℝ))}
  have h0 : (0:ℂ)∈V:=by simp [V,closedEuclideanSector,hβ.le,hβ]
  have hstar : StarConvex ℝ (0:ℂ) V:=by
    intro q hq u v hu hv huv
    simp only [smul_zero,zero_add]
    by_cases hv0 : v=0
    · simpa only [hv0,zero_smul] using h0
    have hvpos : 0<v:=lt_of_le_of_ne hv (Ne.symm hv0)
    have hv1 : v≤1:=by linarith
    have harg : Complex.arg (v • q)=Complex.arg q:=by
      rw [Complex.real_smul]
      exact Complex.arg_real_mul q hvpos
    have hnorm : ‖v • q‖≤‖q‖:=by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hv]
      exact mul_le_of_le_one_left (norm_nonneg q) hv1
    refine ⟨?_,?_⟩
    · change 0≤Complex.arg (v • q) ∧ Complex.arg (v • q)≤β
      rw [harg]
      exact hq.1
    · rcases hq.2 with hqarg | hqn
      · exact Or.inl (harg.symm ▸ hqarg)
      · exact Or.inr (hnorm.trans_lt hqn)
  have hV : IsConnected V:=(hstar.isPathConnected h0).isConnected
  letI : ConnectedSpace V:=isConnected_iff_connectedSpace.mp hV
  let i : V → closedEuclideanSector β:=fun q ↦ ⟨q.1,q.2.1⟩
  have hi : Continuous i:=continuous_subtype_val.subtype_mk _
  have himage : range (σ ∘ i)=range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t)):=by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      refine ⟨mem_range_self (i q),?_⟩
      rintro ⟨t,ht⟩
      have he:=congrArg Subtype.val (hinj ht)
      change sectorPolar ((r:ℝ)+(t:ℝ)) β=q.1 at he
      have hn : (r:ℝ)+(t:ℝ)=‖q.1‖ :=
        (sectorPolar_norm (show (0:ℝ)≤(r:ℝ)+(t:ℝ) from add_nonneg r.2 t.2) β).symm.trans
          (congrArg norm he)
      have harg : β=Complex.arg q.1 :=
        (sectorPolar_arg (r := (r:ℝ)+(t:ℝ)) (θ := β)
          (add_pos_of_pos_of_nonneg hr t.2) ⟨by linarith [Real.pi_pos],hβπ⟩).symm.trans
          (congrArg Complex.arg he)
      rcases q.2.2 with h | h
      · exact h.ne harg.symm
      · linarith [t.2]
    · rintro ⟨⟨q,rfl⟩,hnot⟩
      have hVq : q.1∈V:=by
        refine ⟨q.2,?_⟩
        by_cases hn : ‖q.1‖<(r:ℝ)
        · exact Or.inr hn
        · left
          apply lt_of_le_of_ne q.2.2
          intro he
          apply hnot
          let t : NNReal:=⟨‖q.1‖-(r:ℝ),sub_nonneg.mpr (le_of_not_gt hn)⟩
          refine ⟨t,congrArg σ (Subtype.ext ?_)⟩
          change sectorPolar ((r:ℝ)+(‖q.1‖-(r:ℝ))) β=q.1
          rw [show (r:ℝ)+(‖q.1‖-(r:ℝ))=‖q.1‖ by ring]
          exact (congrArg (sectorPolar ‖q.1‖) he.symm).trans (sectorPolar_norm_arg q.1)
      exact ⟨⟨q.1,hVq⟩,rfl⟩
  rw [← himage]
  exact isConnected_range (hσ.comp hi)

/-- Actual relative openness of S minus its tail. Fullness at the original
apex and compact upper-prefix points is derived, not supplied as a property of
the residual. The closed tail is removed only AFTER obtaining local filling. -/
theorem pointDisappearingSector_without_tail_relative_open
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0<β) (hβπ : β≤Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z,(pointSmoothConformalEDist a y (σ x) (σ z)).toReal=dist x z)
    {P : Set ℂ} (hσP : ∀ x,σ x∈P)
    (hbottom : ∀ t : NNReal,σ (retainedApexBottomSource hβ.le hβπ t)∈frontier P)
    (hOld : ∀ p∈frontier P,∃ C : PointRetainedConeNeighborhood a y P p,C.Admissible)
    (hregular : ∀ x : closedEuclideanSector β,0<‖x.1‖ → 0<Complex.arg x.1 → Complex.arg x.1<β →
      σ x∈interior P ∧ coalescedPointExponent a y (σ x)=0)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hfull : C.flatPhysicalWidth=β)
    (r : NNReal) (hr : 0<(r:ℝ))
    (hprefix : ∀ t : NNReal,t≤r → σ (retainedApexUpperSource hβ.le hβπ t)∈frontier P) :
    IsOpen {z : P | z.1∈range σ\range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t))} := by
  let S:=range σ
  let top : NNReal → ℂ:=fun t ↦ σ (retainedApexUpperSource hβ.le hβπ t)
  let T:=range (fun t : NNReal ↦ σ (disappearingSectorTail hβ.le hβπ r t))
  have hTmetric (u v : NNReal) :
      (pointSmoothConformalEDist a y (σ (disappearingSectorTail hβ.le hβπ r u))
        (σ (disappearingSectorTail hβ.le hβπ r v))).toReal=dist u v:=
    (hσ _ _).trans ((disappearingSectorTail_isometry hβ.le hβπ r).dist_eq u v)
  have hTclosed : IsClosed T:=(pointMetricRay_isClosedEmbedding ha y _ hTmetric).isClosed_range
  have hTsub : T⊆range top:=by rintro x ⟨u,rfl⟩; exact ⟨r+u,rfl⟩
  have hTpre : IsClosed {z : P | z.1∈T}:=hTclosed.preimage continuous_subtype_val
  have hWopen:=pointRetainedSector_without_free_ray_relative_open ha y hβ hβπ σ hσ hσP
    hbottom hOld hregular
  have hopen : @IsOpen P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
      {z : P | z.1∈S\T}:=by
    letI : MetricSpace P:=pointRegionMetricSpace ha y P
    letI : PseudoMetricSpace P:=(pointRegionMetricSpace ha y P).toPseudoMetricSpace
    letI : PseudoEMetricSpace P:=(pointRegionMetricSpace ha y P).toPseudoEMetricSpace
    letI : TopologicalSpace P:=(pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace
    have hWm : IsOpen {z : P | z.1∈S\range top}:=by
      change @IsOpen P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace _
      rw [pointRegionMetricSpace_topology ha y P]
      exact hWopen
    have hTm : IsClosed {z : P | z.1∈T}:=by
      change @IsClosed P (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace _
      rw [pointRegionMetricSpace_topology ha y P]
      exact hTpre
    apply isOpen_iff_mem_nhds.mpr
    rintro q ⟨hqS,hqT⟩
    by_cases hqtop : q.1∈range top
    · obtain ⟨t,htq⟩:=hqtop
      have htr : t<r:=by
        by_contra hn
        have hrt : r≤t:=le_of_not_gt hn
        apply hqT
        let u : NNReal:=⟨(t:ℝ)-(r:ℝ),sub_nonneg.mpr hrt⟩
        refine ⟨u,?_⟩
        have he : r+u=t:=Subtype.ext (by change (r:ℝ)+((t:ℝ)-(r:ℝ))=t; ring)
        change top (r+u)=q.1
        rwa [he]
      have hfill : ∃ ε : ℝ,0<ε ∧ ∀ z,
          (pointSmoothConformalEDist a y z q.1).toReal≤ε → (z∈S ↔ z∈P):=by
        by_cases ht0 : t=0
        · have hqp : q.1=σ (flatLinkSectorApex hβ.le):=by
            rw [ht0] at htq
            have he : retainedApexUpperSource hβ.le hβπ 0=flatLinkSectorApex hβ.le:=Subtype.ext (sectorPolar_zero β)
            change σ (retainedApexUpperSource hβ.le hβπ 0)=q.1 at htq
            rw [he] at htq
            exact htq.symm
          rw [hqp]
          exact pointDisappearingApex_sector_locally_full ha y hβ hβπ σ hσ hσP hbottom C hC hfull
        · have htpos : 0<(t:ℝ):=lt_of_le_of_ne t.2 (fun he ↦ ht0 (Subtype.ext he.symm))
          obtain ⟨D,hD⟩:=hOld _ (hprefix t htr.le)
          have hout:=(pointDisappearingApex_upper_prefix_full ha y hβ hβπ σ hσ hσP r
            hprefix t htpos htr D hD).2
          have htq' : σ (retainedApexUpperSource hβ.le hβπ t)=q.1 := htq
          rw [htq'] at hout
          exact hout
      obtain ⟨ε,hε,hfill⟩:=hfill
      apply Filter.mem_of_superset
        (Filter.inter_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) (hTm.isOpen_compl.mem_nhds hqT))
      intro z hz
      exact ⟨(hfill z.1 hz.1.le).mpr z.2,hz.2⟩
    · exact Filter.mem_of_superset (hWm.mem_nhds ⟨hqS,hqtop⟩)
        (fun z hz ↦ ⟨hz.1,fun ht ↦ hz.2 (hTsub ht)⟩)
  rwa [pointRegionMetricSpace_topology ha y P] at hopen

end RepulsiveCoulomb
