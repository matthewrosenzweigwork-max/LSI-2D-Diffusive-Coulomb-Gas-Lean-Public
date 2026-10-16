module

public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorPointwiseGerms
public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorRelativeOpenness
public import LeanResearch.RepulsiveCoulomb.PointActualSectorReturnObstruction
public import LeanResearch.RepulsiveCoulomb.PointSectorReturnGermWidthIdentification

@[expose] public section

/-!
SOURCE-ONLY, NOT COMPILED. Exact retained-apex contact for the ACTUAL supplied
closed sector. Source isometry constructs both rays and stopped geodesic edges;
actual source/chart germs identify the initial direction with beta; finite old
boundary geometry constructs first contact; actual signed finite GB excludes it.
No contact, cap, angle, total-turn bound, or no-return certificate is an input.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem retainedApexBottomSource_isometry {β : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Isometry (retainedApexBottomSource hβ hβπ) := by
  apply Isometry.of_dist_eq
  intro r s
  change dist (sectorPolar r 0) (sectorPolar s 0) = dist (r:ℝ) (s:ℝ)
  simp only [sectorPolar,conePhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  exact Complex.isometry_ofReal.dist_eq _ _

/-- The positive free ray never returns to the old boundary. The original
signed invariant and beta<=alpha(apex) are the only budget hypotheses. -/
theorem pointRetainedSector_free_ray_no_old_boundary
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hβbudget : β ≤ α (σ (flatLinkSectorApex hβ.le)))
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi-(1+coalescedPointExponent a y p/2)*(K.hi-K.lo)) :
    ∀ u : NNReal, 0 < (u:ℝ) → σ (retainedApexUpperSource hβ.le hβπ u) ∉ frontier P := by
  let p := σ (flatLinkSectorApex hβ.le)
  let top := fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)
  let bottom := fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)
  let upper : ℝ → ℂ := fun u ↦ top u.toNNReal
  let lower : ℝ → ℂ := fun u ↦ bottom u.toNNReal
  have htop0 : top 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero β))
  have hbottom0 : bottom 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero 0))
  have htopmetric (u v : NNReal) : (pointSmoothConformalEDist a y (top u) (top v)).toReal = dist u v :=
    (hσ _ _).trans ((retainedApexUpperSource_isometry hβ.le hβπ).dist_eq u v)
  have hbottommetric (u v : NNReal) : (pointSmoothConformalEDist a y (bottom u) (bottom v)).toReal = dist u v :=
    (hσ _ _).trans ((retainedApexBottomSource_isometry hβ.le hβπ).dist_eq u v)
  have htopc := (pointMetricRay_isClosedEmbedding ha y top htopmetric).continuous
  have hbottomc := (pointMetricRay_isClosedEmbedding ha y bottom hbottommetric).continuous
  have hupperc : Continuous upper := htopc.comp continuous_real_toNNReal
  have hlowerc : Continuous lower := hbottomc.comp continuous_real_toNNReal
  have hupperd : ∀ u ∈ Ici (0:ℝ), ∀ v ∈ Ici (0:ℝ),
      (pointSmoothConformalEDist a y (upper u) (upper v)).toReal = dist u v := by
    intro u hu v hv
    rw [htopmetric]
    change dist ((u.toNNReal:NNReal):ℝ) ((v.toNNReal:NNReal):ℝ) = dist u v
    rw [Real.coe_toNNReal _ hu,Real.coe_toNNReal _ hv]
  have hlowerd : ∀ u ∈ Ici (0:ℝ), ∀ v ∈ Ici (0:ℝ),
      (pointSmoothConformalEDist a y (lower u) (lower v)).toReal = dist u v := by
    intro u hu v hv
    rw [hbottommetric]
    change dist ((u.toNNReal:NNReal):ℝ) ((v.toNNReal:NNReal):ℝ) = dist u v
    rw [Real.coe_toNNReal _ hu,Real.coe_toNNReal _ hv]
  have hupper0 : upper 0 = p := by simpa only [upper,Real.toNNReal_zero] using htop0
  have hlower0 : lower 0 = p := by simpa only [lower,Real.toNNReal_zero] using hbottom0
  obtain ⟨δ,cut,endpoint,hδ,hδC,hcut,hend,hformula,htopg,hbottomg⟩ :=
    pointRetainedSector_actual_two_ray_germs ha y hβ hβπ σ hσ hσP hbottom C hC hremain
  have hupperg : ∀ u ∈ Ioo (0:ℝ) δ, C.chart (upper u) = pointRadialSectorPoint u cut := by
    intro u hu
    have ht : ((u.toNNReal:NNReal):ℝ) = u := Real.coe_toNNReal _ hu.1.le
    simpa only [ht] using htopg u.toNNReal (ht.le.trans hu.2.le)
  have hlowerg : ∀ u ∈ Ioo (0:ℝ) δ, C.chart (lower u) = pointRadialSectorPoint u endpoint := by
    intro u hu
    have ht : ((u.toNNReal:NNReal):ℝ) = u := Real.coe_toNNReal _ hu.1.le
    simpa only [ht] using hbottomg u.toNNReal (ht.le.trans hu.2.le)
  have hentry (u : ℝ) (hu : u ∈ Ioo (0:ℝ) δ) : upper u ∈ interior P := by
    have hd : (pointSmoothConformalEDist a y (upper u) p).toReal = u := by
      rw [← hupper0,hupperd u hu.1.le 0 (le_refl (0 : ℝ)),Real.dist_eq,sub_zero,abs_of_pos hu.1]
    exact C.mem_interior_of_strict_radial_coordinate (hd.trans_lt (hu.2.trans hδC))
      hu.1 hcut (hupperg u hu)
  have hterminal : ∀ t, 0 < t → ¬ Icc (0:ℝ) t ⊆ upper ⁻¹' frontier P := by
    intro t ht hsub
    let u := min δ t/2
    have hu : 0 < u := half_pos (lt_min hδ ht)
    have huδ : u < δ := by dsimp [u]; linarith [min_le_left δ t,lt_min hδ ht]
    have hut : u ≤ t := by dsimp [u]; linarith [min_le_right δ t,lt_min hδ ht]
    exact (hsub ⟨hu.le,hut⟩).2 (hentry u ⟨hu,huδ⟩)
  intro v hv hvfront
  have hlater : ∃ t, 0 < t ∧ upper t ∈ frontier P := by
    refine ⟨v,hv,?_⟩
    simpa only [upper,Real.toNNReal_coe] using hvfront
  obtain ⟨w,hw,hwfront,_,hgap⟩ := exists_pointMetricRay_first_later_boundary_contact
    ha y pieces hpieces upper hupperc hupperd (z:=0) le_rfl hterminal hlater
  let R : NNReal := ⟨w,hw.le⟩
  let E₀ := pointMetricRaySegment ha y top htopmetric R hw
  have hE₀0 : E₀.start = p := htop0
  let E : PointGeodesicTreeEdge a y :=
    { E₀ with
      start := p
      distinct := fun he ↦ E₀.distinct (hE₀0.trans he)
      curve_start := E₀.curve_start.trans hE₀0
      geodesic := by
        intro s t
        rw [← hE₀0]
        exact E₀.geodesic s t }
  have hEP : ∀ t, E.curve t ∈ P := fun t ↦ hσP _
  have hElen : pointActualEdgeLength E = w := by
    change (pointSmoothConformalEDist a y p (top R)).toReal = w
    rw [← htop0,htopmetric,NNReal.dist_eq,NNReal.coe_zero,zero_sub,abs_neg]
    change |w| = w
    exact abs_of_pos hw
  have hEcurve : E.curve = lineCapSegment upper 0 w := by
    funext t
    apply congrArg top
    apply Subtype.ext
    change w*t.1 = ((0+t.1*(w-0)).toNNReal:ℝ)
    rw [sub_zero,zero_add,Real.coe_toNNReal _ (mul_nonneg t.2.1 hw.le)]
    ring
  have hEclock : ∀ t : unitInterval, E.curve t = upper (pointActualEdgeLength E*t.1) := by
    intro t
    rw [hElen]
    apply congrArg top
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (mul_nonneg hw.le t.2.1)).symm
  let F := pointRayComparisonEdge ha y bottom hbottommetric E
  have hF0 : F.start = E.start := hbottom0
  have hFP : ∀ t, F.curve t ∈ P := fun t ↦ hσP _
  have hFclock : ∀ t : unitInterval, F.curve t = lower (pointActualEdgeLength F*t.1) := by
    intro t
    rw [pointRayComparisonEdge_length]
    apply congrArg bottom
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1)).symm
  have hrawF := C.reference_angle_eq_actual_clean_germ ha y hC F hF0 hFP lower hFclock hδ hend hlowerg
  obtain ⟨hrawE,_,hwidth⟩ := C.sector_width_eq_actual_germ_direction ha y hC E rfl hEP
    upper lower hEclock hδ hδ hβ.le ⟨hcut.1.le,hcut.2.le⟩ hend hend hupperg hlowerg hlowerg hformula
  have hφopen : C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi := hrawE.symm ▸ hcut
  have hdirection : C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP ≤ α E.start := by
    have he : C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP = β := by
      unfold PointRetainedConeNeighborhood.actualPhysicalDirection
      rw [hrawF,add_comm (coalescedPointExponent a y p/2) 1]
      exact hwidth
    rw [he]
    exact hβbudget
  have hrw : upper w = E.finish := by
    apply congrArg top
    apply Subtype.ext
    exact Real.coe_toNNReal _ hw.le
  have hfinish : E.finish ∈ frontier P := hrw ▸ hwfront
  exact not_actual_sector_return_of_signed_budget ha y H hHP pieces hpieces E F hEP hF0 hFP
    C hC hφopen lower upper hlowerc hupperc hlower0 hlowerd (fun u hu ↦ hbottom _)
    hFclock hw hEcurve hupper0 hrw
    (fun u hu z hz ↦ hupperd u hu.1 z hz.1) hgap hfinish hbudget hν hdirection

/-- Exact contact of the supplied closed sector with the old boundary.
The original open-sector interior condition is used only to exclude contacts
through its open two-dimensional part. The free-ray exclusion is proved above. -/
theorem pointRetainedSector_exact_old_boundary_contact
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (hinterior : ∀ x : closedEuclideanSector β,
      0 < ‖x.1‖ → 0 < Complex.arg x.1 → Complex.arg x.1 < β → σ x ∈ interior P)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hβbudget : β ≤ α (σ (flatLinkSectorApex hβ.le)))
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi-(1+coalescedPointExponent a y p/2)*(K.hi-K.lo)) :
    range σ ∩ frontier P =
      range (fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)) := by
  have hno := pointRetainedSector_free_ray_no_old_boundary ha y hβ hβπ σ hσ H hHP hσP
    hbottom pieces hpieces C hC hremain hbudget hβbudget hν
  ext z
  constructor
  · rintro ⟨⟨x,rfl⟩,hxF⟩
    by_cases hx0 : x.1 = 0
    · refine ⟨0,congrArg σ (Subtype.ext ?_)⟩
      change sectorPolar 0 0 = x.1
      rw [sectorPolar_zero,hx0]
    by_cases ha0 : Complex.arg x.1 = 0
    · refine ⟨⟨‖x.1‖,norm_nonneg _⟩,congrArg σ (Subtype.ext ?_)⟩
      change sectorPolar ‖x.1‖ 0 = x.1
      rw [← ha0,sectorPolar_norm_arg]
    by_cases haβ : Complex.arg x.1 = β
    · have he : retainedApexUpperSource hβ.le hβπ ⟨‖x.1‖,norm_nonneg _⟩ = x := by
        apply Subtype.ext
        change sectorPolar ‖x.1‖ β = x.1
        exact (congrArg (sectorPolar ‖x.1‖) haβ).symm.trans (sectorPolar_norm_arg x.1)
      exact False.elim (hno ⟨‖x.1‖,norm_nonneg _⟩ (norm_pos_iff.mpr hx0) (he.symm ▸ hxF))
    · exact False.elim (hxF.2 (hinterior x (norm_pos_iff.mpr hx0)
        (lt_of_le_of_ne x.2.1 (Ne.symm ha0)) (lt_of_le_of_ne x.2.2 haβ)))
  · rintro ⟨u,rfl⟩
    exact ⟨mem_range_self _,hbottom u⟩

end RepulsiveCoulomb
