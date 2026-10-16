module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripStateAdapters

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. A companion to the frozen actual translated
strip endpoint, with exactly the same geometric assumptions. It retains the
constructed two-sided ambient straightening and packages the reusable signed
halfplane state. Every set is the literal closure(P \ range F).

The top ray may contain marked points. Its positive-time points retain their
old interior coefficients and receive full complementary interval charts.
Existence of a maximal strip, attained marked contact, or a next clean ray is
not claimed. The exact old and new geometric state is exposed for those steps. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Concrete output data, not a cut hypothesis. The result retains the actual
Schoenflies sides as well as the new ambient halfplane representation. -/
structure PointTranslatedStripIterationOutput {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (P S Q : Set ℂ)
    (τ : NNReal → ℂ) (p : ℂ) (ν μ α : ℂ →₀ ℝ) (θ : ℝ)
    (Cz : PointRetainedConeNeighborhood a y P (τ 0)) where
  old_forward : NNReal → ℂ
  old_forward_closed : IsClosedEmbedding old_forward
  old_forward_zero : old_forward 0 = τ 0
  old_forward_range : range old_forward = insert (τ 0) (frontier P \ S)
  old_forward_meet : range old_forward ∩ S = {τ 0}
  sides : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin τ old_forward)
  removed_side : Pᶜ ∪ (S \ range τ) = sides.positive
  kept_side : interior P \ S = sides.negative
  residual_closure : Q = closure (P \ S)
  residual_side : Q = closure sides.negative
  state : PointRetainedSignedHalfplaneState a y Q μ α
  state_ambient : state.ambient = sides.negativeAmbientStraightening
  literal_union : Q = (P \ S) ∪ range τ
  literal_difference : Q = P \ (S \ range τ)
  subset_old : Q ⊆ P
  interior_eq : interior Q = interior P \ S
  frontier_eq : frontier Q = range τ ∪ range old_forward
  apex_removed : p ∉ Q
  origin_retained : τ 0 ∈ frontier Q
  apex_old_frontier : p ∈ frontier P
  origin_old_frontier : τ 0 ∈ frontier P
  apex_ne_origin : p ≠ τ 0
  top_closed : IsClosedEmbedding τ
  top_metric : ∀ r s, (pointSmoothConformalEDist a y (τ r) (τ s)).toReal = dist r s
  top_frontier : range τ ⊆ frontier Q
  open_top_old_interior : ∀ r, 0 < r → τ r ∈ interior P
  open_top_coeff : ∀ r, 0 < r → μ (τ r) = ν (τ r)
  corner_chart : ∃ E : PointRetainedConeNeighborhood a y Q (τ 0),
    E.chart = Cz.chart ∧ E.flatPhysicalWidth = Cz.flatPhysicalWidth - θ ∧
    E.Admissible ∧ μ (τ 0) = Real.pi - E.flatPhysicalWidth
  open_top_chart : ∀ r, 0 < r →
    ∃ E : PointRetainedConeNeighborhood a y Q (τ r),
      E.flatPhysicalWidth =
        (coalescedPointExponent a y (τ r) / 2 + 1) * (2 * Real.pi) - Real.pi ∧
      E.Admissible ∧ μ (τ r) = Real.pi - E.flatPhysicalWidth
  transfer_amount : ν p = θ
  transfer_exact : μ = ν + Finsupp.single (τ 0) θ - Finsupp.single p θ
  negative_nonincrease : ∀ x, pointSignedNegativePart μ x ≤ pointSignedNegativePart ν x
  curvature_mass : pointSignedCurvatureMass μ α = pointSignedCurvatureMass ν α
  allocation_mass : pointSignedBudgetMass μ α = pointSignedBudgetMass ν α
  budget_invariant : PointSignedBudgetInvariant ν α → PointSignedBudgetInvariant μ α

/-- Same actual input assumptions as the frozen endpoint. The new conclusion
keeps the witnesses that the earlier final conjunction discarded. -/
theorem pointTranslatedStrip_actual_iteration_output
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ≃ₜℂ) (hHP : P=H ⁻¹' planarClosedUpperHalfplane)
    {stripAngle b : ℝ} (stripAngle_pos : 0<stripAngle) (stripAngle_lt_pi : stripAngle<Real.pi) (hb : 0<b)
    (F : flatShearedStrip (conePhase stripAngle) b→P)
    (hF : ∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z)
    (hcontact : range (fun x ↦ (F x).1) ∩ frontier P=
      range (fun r ↦ (F (translatedStripBottom hb.le r)).1) ∪
      range (fun u ↦ (F (translatedStripEdge u)).1))
    (ν α : ℂ→₀ℝ)
    (hνI : ∀ x∈interior P,ν x= -Real.pi*coalescedPointExponent a y x)
    (hνB : ∀ x∈frontier P,∃ C : PointRetainedConeNeighborhood a y P x,
      C.Admissible ∧ ν x=Real.pi-C.flatPhysicalWidth)
    (hνO : ∀ x,x∉P → ν x=0)
    (Cz : PointRetainedConeNeighborhood a y P (F (translatedStripTop hb.le 0)).1)
    (hCz : Cz.Admissible) (hνz : ν (F (translatedStripTop hb.le 0)).1=Real.pi-Cz.flatPhysicalWidth)
    (hremain : Real.pi-stripAngle<Cz.flatPhysicalWidth)
    (hαP : ∀ x,α x≠0 → x∈P)
    (hαp : α (F (translatedStripBottom hb.le 0)).1=0)
    (hclean : ∀ x∈range (fun q ↦ (F q).1) \ range (fun r ↦ (F (translatedStripTop hb.le r)).1),
      x≠(F (translatedStripBottom hb.le 0)).1 → ν x=0 ∧ α x=0) :
    let S := range (fun x ↦ (F x).1)
    let τ : NNReal → ℂ := fun r ↦ (F (translatedStripTop hb.le r)).1
    let Q := closure (P \ S)
    let p := (F (translatedStripBottom hb.le 0)).1
    let μ := BoundaryPreparation.transfer ν p (τ 0)
    Nonempty (PointTranslatedStripIterationOutput a y P S Q τ p ν μ α (Real.pi-stripAngle) Cz) ∧
      (∀ r, (F (translatedStripBottom hb.le r)).1 ∉ Q) ∧
      (∀ u : Icc (0:ℝ) b, u.1<b → (F (translatedStripEdge u)).1 ∉ Q) := by
  let S := range (fun x ↦ (F x).1)
  let τ : NNReal → ℂ := fun r ↦ (F (translatedStripTop hb.le r)).1
  let Q := closure (P \ S)
  let p := (F (translatedStripBottom hb.le 0)).1
  let μ := BoundaryPreparation.transfer ν p (τ 0)
  obtain ⟨g₀, hg₀, hg₀0, hg₀range, hQdiff₀, hQP₀, hQI₀, hQfront₀,
      hhomeo, hpQ, hzQ, hedge, hall, hpturn, htransfer, hμI, hμB, hμO,
      hnegative, hmass, hbudget⟩ :=
    pointTranslatedStrip_actual_residual_and_all_point_update ha y H hHP stripAngle_pos stripAngle_lt_pi hb
      F hF hcontact ν α hνI hνB hνO Cz hCz hνz hremain hαP hαp hclean
  have hpfront : p ∈ frontier P := by
    have hm : p ∈ S ∩ frontier P := hcontact.symm ▸ Or.inl ⟨0,rfl⟩
    exact hm.2
  have hzfront : τ 0 ∈ frontier P := by
    let u : Icc (0:ℝ) b := ⟨b,hb.le,le_rfl⟩
    have he : translatedStripEdge (v := conePhase stripAngle) u = translatedStripTop hb.le 0 := Subtype.ext rfl
    have hm : (F (translatedStripEdge u)).1 ∈ S ∩ frontier P :=
      hcontact.symm ▸ Or.inr ⟨u,rfl⟩
    simpa only [he] using hm.2
  have hcharts : ∀ x ∈ frontier P,
      ∃ C : PointRetainedConeNeighborhood a y P x, C.Admissible := by
    intro x hx
    obtain ⟨C,hC,_⟩ := hνB x hx
    exact ⟨C,hC⟩
  have hcleanInterior : ∀ x ∈ interior P,
      x ∈ S \ range τ → coalescedPointExponent a y x = 0 := by
    intro x hxI hxW
    have hxp : x ≠ p := by intro he; exact hpfront.2 (he ▸ hxI)
    have hn := (hclean x hxW hxp).1
    have he := hνI x hxI
    rw [hn] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (neg_ne_zero.mpr Real.pi_ne_zero)
  obtain ⟨g,hg,hg0,hgrange,hgmeet,D,hremoved,hkeep,hclosure,hunion,
      hQdiff,hQP,hQI,hQfront,hhomeoD⟩ :=
    pointTranslatedStrip_actual_cut_topology ha y H hHP stripAngle_pos stripAngle_lt_pi hb F hF hcontact
      hcharts hcleanInterior
  have hQambient : Q = D.negativeAmbientStraightening ⁻¹' planarClosedUpperHalfplane :=
    hclosure.trans D.closure_negative_eq_ambient_upper
  have hQconnected : IsConnected Q := by
    dsimp only [Q, S]
    rw [hclosure]
    exact D.negative_connected.closure
  have hnewcharts : ∀ x ∈ Q, ∃ C : PointRetainedConeNeighborhood a y Q x,
      C.Full ∨ C.Admissible := by
    intro x hx
    by_cases hi : x ∈ interior Q
    · obtain ⟨C,hlo,hhi,_⟩ := pointInterior_construct_full_retained_chart ha y hi
      exact ⟨C,Or.inl (C.full_of_zero_two_pi hlo hhi)⟩
    · obtain ⟨C,hC,_⟩ := hμB x ⟨subset_closure hx,hi⟩
      exact ⟨C,Or.inr hC⟩
  let K : PointRetainedSignedHalfplaneState a y Q μ α :=
    { ambient := D.negativeAmbientStraightening
      region_eq := hQambient
      connected := hQconnected
      charts := hnewcharts
      interior_coeff := hμI
      boundary_coeff := hμB
      exterior_coeff := hμO
      allocation_support := hbudget }
  have hvi : (conePhase stripAngle).im ≠ 0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi stripAngle_pos stripAngle_lt_pi).ne'
  have hFinj := (pointTranslatedStrip_closed_proper ha y hvi F hF).1.injective
  have hpz : p ≠ τ 0 := translatedStrip_apex_ne_top_origin hvi hb hFinj
  have hτmetric : ∀ r s : NNReal,
      (pointSmoothConformalEDist a y (τ r) (τ s)).toReal = dist r s := by
    intro r s
    rw [hF]
    exact (translatedStripTop_isometry hb.le).dist_eq r s
  have hτclosed : IsClosedEmbedding τ := pointMetricRay_isClosedEmbedding ha y τ hτmetric
  have hτfront : range τ ⊆ frontier Q := by
    rw [hQfront]
    exact subset_union_left
  have hfrontFinal : frontier Q = range τ ∪ range g := by
    rw [hQfront,hgrange]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (mem_insert_of_mem _ hx)
    · rintro (hx | hx)
      · exact Or.inl hx
      · rcases mem_insert_iff.mp hx with he | hx
        · exact Or.inl (he.symm ▸ mem_range_self 0)
        · exact Or.inr hx
  have hτinterior : ∀ r : NNReal, 0 < r → τ r ∈ interior P :=
    pointTranslatedStrip_open_top_interior hvi hb F hFinj hcontact
  have hτcoeff : ∀ r : NNReal, 0 < r → μ (τ r) = ν (τ r) := by
    intro r hr
    have hi := hτinterior r hr
    exact BoundaryPreparation.transfer_away ν
      (fun he ↦ hpfront.2 (he ▸ hi)) (fun he ↦ hzfront.2 (he ▸ hi))
  have hcorner : ∃ E : PointRetainedConeNeighborhood a y Q (τ 0),
      E.chart = Cz.chart ∧ E.flatPhysicalWidth = Cz.flatPhysicalWidth - (Real.pi-stripAngle) ∧
      E.Admissible ∧ μ (τ 0) = Real.pi - E.flatPhysicalWidth := by
    obtain ⟨E,hchart,hwidth,hturn,hE⟩ := pointTranslatedStrip_construct_corner_chart
      ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact Cz hCz hremain hQdiff
    refine ⟨E,hchart,hwidth,hE,?_⟩
    rw [BoundaryPreparation.transfer_target ν hpz,hpturn,hνz]
    exact hturn.symm
  have htopcharts : ∀ r : NNReal, 0 < r →
      ∃ E : PointRetainedConeNeighborhood a y Q (τ r),
        E.flatPhysicalWidth =
          (coalescedPointExponent a y (τ r)/2+1)*(2*Real.pi)-Real.pi ∧
        E.Admissible ∧ μ (τ r) = Real.pi-E.flatPhysicalWidth := by
    intro r hr
    obtain ⟨hi,E,hwidth,hturn,hE⟩ := pointTranslatedStrip_construct_open_top_chart
      ha y stripAngle_pos stripAngle_lt_pi hb F hF hcontact hQdiff r hr
    refine ⟨E,hwidth,hE,?_⟩
    rw [hτcoeff r hr,hνI _ hi]
    exact hturn.symm
  have hbottom : ∀ r, (F (translatedStripBottom hb.le r)).1 ∉ Q := by
    intro r hx
    dsimp only [Q, S] at hx
    rw [hQdiff] at hx
    exact hx.2 ⟨mem_range_self _,translatedStrip_bottom_not_top hvi hb hFinj r⟩
  refine ⟨⟨{
    old_forward := g
    old_forward_closed := hg
    old_forward_zero := hg0
    old_forward_range := hgrange
    old_forward_meet := hgmeet
    sides := D
    removed_side := hremoved
    kept_side := hkeep
    residual_closure := rfl
    residual_side := hclosure
    state := K
    state_ambient := rfl
    literal_union := hunion
    literal_difference := hQdiff
    subset_old := hQP
    interior_eq := hQI
    frontier_eq := hfrontFinal
    apex_removed := hpQ
    origin_retained := hzQ
    apex_old_frontier := hpfront
    origin_old_frontier := hzfront
    apex_ne_origin := hpz
    top_closed := hτclosed
    top_metric := hτmetric
    top_frontier := hτfront
    open_top_old_interior := hτinterior
    open_top_coeff := hτcoeff
    corner_chart := hcorner
    open_top_chart := htopcharts
    transfer_amount := hpturn
    transfer_exact := htransfer
    negative_nonincrease := hnegative
    curvature_mass := hmass
    allocation_mass := pointTranslatedStrip_budgetMass_unchanged ν μ α
    budget_invariant := pointTranslatedStrip_budgetInvariant_of_update hnegative hmass
  }⟩,hbottom,hedge⟩

end RepulsiveCoulomb
