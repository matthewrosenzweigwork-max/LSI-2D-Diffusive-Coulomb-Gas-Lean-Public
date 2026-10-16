module

public import LeanResearch.RepulsiveCoulomb.PointFullLinePreparationCharts
public import LeanResearch.RepulsiveCoulomb.PointFullLinePreparationRay

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual full-line preparation, assembled from the
recovered first-contact and literal-residual constructions. The complete metric
parameterization of the ENTIRE old frontier, its ambient halfplane topology,
and its genuine coefficient/chart interpretation remain honest upstream inputs.
No strip, normality, contact, residual, curvature-update, support or clean-ray
certificate is supplied as input. The finite marks are exactly supp ν ∪ supp α.
-/
noncomputable section
open Set Metric Topology
open scoped Classical
namespace RepulsiveCoulomb

/-- Constructed output. `Q` is pinned to the literal closed complement, and
`νQ` is pinned both to its geometric coefficient meaning and to the old ν.
The budget α is the same ambient Finsupp throughout. -/
structure PointFullLinePreparationStep {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (line : ℝ → ℂ) (ν α : ℂ →₀ ℝ) where
  height : ℝ
  height_pos : 0 < height
  strip : flatFullNormalStrip height → P
  strip_metric : ∀ z w,
    (pointSmoothConformalEDist a y (strip z).1 (strip w).1).toReal = dist z w
  bottom : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip height,
    (strip ⟨(r : ℂ), hr⟩).1 = line r
  positive_interior : ∀ z, 0 < z.1.im → (strip z).1 ∈ interior P
  clean_below : ∀ z, z.1.im < height → (strip z).1 ∉ pointSignedMarked ν α
  strip_closed : IsClosedEmbedding (fun z ↦ (strip z).1)
  strip_proper : IsProperMap (fun z ↦ (strip z).1)
  contact : ℂ
  contact_marked : contact ∈ pointSignedMarked ν α
  nearest_clock : ℝ
  nearest_distance : (pointSmoothConformalEDist a y contact (line nearest_clock)).toReal = height
  all_marked_lower_bound : ∀ p ∈ pointSignedMarked ν α, ∀ r : ℝ,
    height ≤ (pointSmoothConformalEDist a y p (line r)).toReal
  top_contact : (strip (fullStripTop height_pos.le nearest_clock)).1 = contact
  Q : Set ℂ
  residual_eq : Q = closure (P \ range (fun z ↦ (strip z).1))
  sides : PlanarLineHalfplaneHomeomorphs (fun r ↦ (strip (fullStripTop height_pos.le r)).1)
  removed_side : Pᶜ ∪ (range (fun z ↦ (strip z).1) \
    range (fun r ↦ (strip (fullStripTop height_pos.le r)).1)) = sides.positive
  open_remainder : P \ range (fun z ↦ (strip z).1) = sides.negative
  closed_remainder : Q = closure sides.negative
  subset_old : Q ⊆ P
  interior_eq : interior Q = P \ range (fun z ↦ (strip z).1)
  frontier_eq : frontier Q = range (fun r ↦ (strip (fullStripTop height_pos.le r)).1)
  halfplane : Nonempty (Q ≃ₜ planarClosedUpperHalfplane)
  contact_frontier : contact ∈ frontier Q
  retained_charts : ∀ p ∈ Q,
    ∃ C : PointRetainedConeNeighborhood a y Q p, C.Full ∨ C.Admissible
  top_retained : ∀ s, ∃ E : PointRetainedConeNeighborhood a y Q
      (strip (fullStripTop height_pos.le s)).1,
    E.flatPhysicalWidth =
      (1 + coalescedPointExponent a y (strip (fullStripTop height_pos.le s)).1 / 2) *
        (2 * Real.pi) - Real.pi ∧
    Real.pi - E.flatPhysicalWidth =
      -Real.pi * coalescedPointExponent a y (strip (fullStripTop height_pos.le s)).1 ∧
    E.Admissible
  νQ : ℂ →₀ ℝ
  νQ_coefficients : ∀ p, νQ p = pointFullStripSignedCoefficient a y Q
    (fun z ↦ -Real.pi * coalescedPointExponent a y z) p
  νQ_representation : PointFullStripCurvatureRepresentation a y Q
    (fun z ↦ -Real.pi * coalescedPointExponent a y z) νQ
  curvature_eq : νQ = ν
  support_eq : νQ.support = ν.support
  support_card_eq : νQ.support.card = ν.support.card
  interior_support_subset : (νQ.support.filter (fun p ↦ p ∈ interior Q)) ⊆
    (ν.support.filter (fun p ↦ p ∈ interior P))
  interior_count_le : (νQ.support.filter (fun p ↦ p ∈ interior Q)).card ≤
    (ν.support.filter (fun p ↦ p ∈ interior P)).card
  preparation_rank_le : νQ.support.card + (νQ.support.filter (fun p ↦ p ∈ interior Q)).card ≤
    ν.support.card + (ν.support.filter (fun p ↦ p ∈ interior P)).card
  marks_eq : pointSignedMarked νQ α = pointSignedMarked ν α
  budget_support_retained : (↑α.support : Set ℂ) ⊆ Q
  budget_invariant : PointSignedBudgetInvariant νQ α
  clean_budget_ray :
    ∃ s : ℝ, let top : ℝ → ℂ := fun r ↦ (strip (fullStripTop height_pos.le r)).1
      top s ∈ pointSignedMarked νQ α ∧ 0 < α (top s) ∧
      (∀ t, top t ∈ pointSignedMarked νQ α → t ≤ s) ∧
      let ρ : NNReal → ℂ := fun t ↦ top (s + (t : ℝ))
      ρ 0 = top s ∧
      (∀ u v, (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v) ∧
      IsClosedEmbedding ρ ∧ IsProperMap ρ ∧ range ρ ⊆ frontier Q ∧
      (∀ t : NNReal, 0 < t → ρ t ∉ pointSignedMarked νQ α) ∧
      Disjoint ((↑(pointSignedMarked νQ α) : Set ℂ) \ {ρ 0}) (range ρ)

/-- The full preparatory cut and its actual clean budget ray are constructed.
The complete minimizing old boundary line is explicit here: it is NOT deduced
from unmarkedness of an arbitrary state's frontier. -/
theorem point_exists_actual_full_line_preparation
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (line : ℝ → ℂ)
    (hline : ∀ r t, (pointSmoothConformalEDist a y (line r) (line t)).toReal = dist r t)
    (hboundary : frontier P = range line)
    (turn : ℂ → ℝ)
    (hturn : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      turn p = Real.pi - C.flatPhysicalWidth)
    (ν α : ℂ →₀ ℝ)
    (hν : PointFullStripCurvatureRepresentation a y P turn ν)
    (hαP : (↑α.support : Set ℂ) ⊆ P)
    (hbudget : PointSignedBudgetInvariant ν α)
    (hclean : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (frontier P)) :
    Nonempty (PointFullLinePreparationStep a y P line ν α) := by
  classical
  have hP : IsClosed P := by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have hconn : IsPreconnected P := by
    rw [hHP]
    apply H.isPreconnected_preimage.mpr
    have hc : Convex ℝ planarClosedUpperHalfplane :=
      convex_halfSpace_ge (.mk Complex.add_im Complex.smul_im) 0
    exact hc.isPreconnected
  have hcharts := pointFullLine_old_full_or_admissible_charts ha y hν hturn hclean
  have hmarkedI := hν.interior_marked α
  have hmarkedB := hν.boundary_marked α
  have hmarksP : (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P :=
    pointSignedMarked_subset
      (fun p hp ↦ hν.support_subset (Finsupp.mem_support_iff.mpr hp))
      (fun p hp ↦ hαP (Finsupp.mem_support_iff.mpr hp))
  have hcleanLine : Disjoint (↑(pointSignedMarked ν α) : Set ℂ) (range line) := by
    rwa [← hboundary]
  have hturn' : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      turn p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo) := by
    intro p hp
    obtain ⟨C, hC⟩ := hturn p hp
    refine ⟨C, ?_⟩
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y p / 2) 1] using hC
  obtain ⟨h, hh, x, hx, r, hdist, hbound, F, hF, hb, hi, hav, hcontact, hc, hp⟩ :=
    point_exists_marked_first_contact_full_strip ha y hP hconn hcharts line hline hboundary
      turn hturn' (pointSignedMarked ν α).finite_toSet
      (pointFullLine_actual_marks_nonempty hbudget.budget_pos) hmarksP hmarkedI hmarkedB hcleanLine
  have hbottom (s : ℝ) : (F (fullStripBottom hh.le s)).1 = line s := hb s _
  have hbottomBoundary : frontier P = range (fun s ↦ (F (fullStripBottom hh.le s)).1) := by
    have he : (fun s ↦ (F (fullStripBottom hh.le s)).1) = line := funext hbottom
    rw [he, hboundary]
  have htopContact : (F (fullStripTop hh.le r)).1 = x := by
    rw [pointFullLine_top_point_eq hh.le r] at hcontact
    exact hcontact
  let Q : Set ℂ := closure (P \ range (fun z ↦ (F z).1))
  let top : ℝ → ℂ := fun s ↦ (F (fullStripTop hh.le s)).1
  obtain ⟨D, htop, hremoved, hopen, hclosed, hQP, hQI, hQfront, hhomeo,
    _, hwidths, hcoeff, hαQ⟩ :=
    pointFullStrip_actual_residual_and_all_point_update ha y H hHP hh F hF hbottomBoundary
      turn hturn (↑(pointSignedMarked ν α) : Set ℂ) (↑α.support : Set ℂ)
      hmarkedI hmarkedB (fun s ↦ hav (fullStripBottom hh.le s) hh)
      (fun z _ hz ↦ hav z hz) hαP (pointFullLine_budget_subset_actual_marks ν α)
  have hxfront : x ∈ frontier Q := by
    rw [hQfront]
    exact ⟨r, htopContact⟩
  have htopI : range top ⊆ interior P := by
    rintro p ⟨s, rfl⟩
    exact hi (fullStripTop hh.le s) hh
  have htopE : ∀ s, ∃ E : PointRetainedConeNeighborhood a y Q (top s),
      E.flatPhysicalWidth = (1 + coalescedPointExponent a y (top s) / 2) * (2 * Real.pi) - Real.pi ∧
      Real.pi - E.flatPhysicalWidth = -Real.pi * coalescedPointExponent a y (top s) ∧ E.Admissible := by
    intro s
    obtain ⟨C, E, _, _, _, hE, ht, hA⟩ := hwidths s
    exact ⟨E, hE, ht, hA⟩
  have hQcharts : ∀ p ∈ Q, ∃ C : PointRetainedConeNeighborhood a y Q p,
      C.Full ∨ C.Admissible := by
    intro p hpQ
    by_cases hpI : p ∈ interior Q
    · obtain ⟨C, hC⟩ := pointFullLine_interior_full_chart ha y hpI
      exact ⟨C, Or.inl hC⟩
    · have hpF : p ∈ frontier Q := ⟨subset_closure hpQ, hpI⟩
      obtain ⟨s, hs⟩ := (hQfront ▸ hpF : p ∈ range top)
      subst p
      obtain ⟨E, _, _, hE⟩ := htopE s
      exact ⟨E, Or.inr hE⟩
  let cQ := pointFullStripSignedCoefficient a y Q
    (fun z ↦ -Real.pi * coalescedPointExponent a y z)
  have hcQ : ∀ p, cQ p = ν p := fun p ↦ (hcoeff p).trans (hν.coefficient_eq hP p)
  let νQ := pointFullStripFinsuppOfCoefficient ν cQ hcQ
  have hνQ : νQ = ν := pointFullStripFinsuppOfCoefficient_eq ν cQ hcQ
  have hνQc : ∀ p, νQ p = cQ p := fun _ ↦ rfl
  have hQrep : PointFullStripCurvatureRepresentation a y Q
      (fun z ↦ -Real.pi * coalescedPointExponent a y z) νQ :=
    PointFullStripCurvatureRepresentation.of_coefficient_eq isClosed_closure hνQc
  obtain ⟨hsupp, hcard, hinteriorSupp, hinteriorCard, hrank⟩ :=
    pointFullStrip_support_and_interior_counts hνQ hQP
  obtain ⟨s, hsmark, hsα, hsmax, hρ0, hρmetric, hρclosed, hρproper,
    hρfront, _, hρclean, _, hρdis, _⟩ :=
    pointFullLine_exists_clean_budget_ray ha y hν hbudget.dominates top htop
      (by rw [hQfront]) htopI ⟨r, by
        change (F (fullStripTop hh.le r)).1 ∈ pointSignedMarked ν α
        rw [htopContact]
        exact hx⟩
  refine ⟨{
    height := h
    height_pos := hh
    strip := F
    strip_metric := hF
    bottom := hb
    positive_interior := hi
    clean_below := hav
    strip_closed := hc
    strip_proper := hp
    contact := x
    contact_marked := hx
    nearest_clock := r
    nearest_distance := hdist
    all_marked_lower_bound := hbound
    top_contact := htopContact
    Q := Q
    residual_eq := rfl
    sides := D
    removed_side := hremoved
    open_remainder := hopen
    closed_remainder := hclosed
    subset_old := hQP
    interior_eq := hQI
    frontier_eq := hQfront
    halfplane := hhomeo
    contact_frontier := hxfront
    retained_charts := hQcharts
    top_retained := htopE
    νQ := νQ
    νQ_coefficients := hνQc
    νQ_representation := hQrep
    curvature_eq := hνQ
    support_eq := hsupp
    support_card_eq := hcard
    interior_support_subset := hinteriorSupp
    interior_count_le := hinteriorCard
    preparation_rank_le := hrank
    marks_eq := by rw [hνQ]
    budget_support_retained := hαQ
    budget_invariant := by rw [hνQ]; exact hbudget
    clean_budget_ray := ?_ }⟩
  refine ⟨s, ?_⟩
  dsimp only
  rw [hνQ]
  exact ⟨hsmark, hsα, hsmax, hρ0, hρmetric, hρclosed, hρproper, hρfront, hρclean, hρdis⟩

namespace PointFullLinePreparationStep
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ}
  {line : ℝ → ℂ} {ν α : ℂ →₀ ℝ}

/-- Normality is derived after actual contact: every minimizing segment
from the attained nearest bottom point is the literal vertical strip segment. -/
theorem minimizer_is_vertical (ha : ∀ j, 0 ≤ a j)
    (R : PointFullLinePreparationStep a y P line ν α)
    (γ : unitInterval → ℂ) (h0 : γ 0 = line R.nearest_clock) (h1 : γ 1 = R.contact)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y (line R.nearest_clock) R.contact).toReal) :
    ∀ t, γ t = (R.strip (fullStripPoint R.nearest_clock
      ⟨t.1 * R.height, mul_nonneg t.2.1 R.height_pos.le,
        mul_le_of_le_one_left R.height_pos.le t.2.2⟩)).1 := by
  apply pointFullStrip_minimizer_is_vertical ha y R.height_pos R.strip R.strip_metric
    line R.bottom R.nearest_clock R.contact ?_ γ h0 h1 hd
  rw [pointFullLine_top_point_eq]
  exact R.top_contact

/-- Both actual finite supports remain on the literal closed residual. -/
theorem actual_marked_subset (R : PointFullLinePreparationStep a y P line ν α) :
    (↑(pointSignedMarked R.νQ α) : Set ℂ) ⊆ R.Q :=
  pointSignedMarked_subset
    (fun p hp ↦ R.νQ_representation.support_subset (Finsupp.mem_support_iff.mpr hp))
    (fun p hp ↦ R.budget_support_retained (Finsupp.mem_support_iff.mpr hp))

/-- The new whole boundary has the actual all-pairs ambient metric law. -/
theorem top_metric (R : PointFullLinePreparationStep a y P line ν α) :
    ∀ s t, (pointSmoothConformalEDist a y
      (R.strip (fullStripTop R.height_pos.le s)).1
      (R.strip (fullStripTop R.height_pos.le t)).1).toReal = dist s t := by
  intro s t
  rw [R.strip_metric]
  exact (fullStripTop_isometry R.height_pos.le).dist_eq s t

/-- The residual retains an ambient straightening, not only a subtype
homeomorphism. It is the actual top-line straightening followed by conjugation. -/
theorem ambient_halfplane (R : PointFullLinePreparationStep a y P line ν α) :
    R.Q = (R.sides.straightening.trans Complex.conjCLE.toHomeomorph) ⁻¹'
      planarClosedUpperHalfplane := by
  rw [R.closed_remainder, R.sides.negative_eq, ← R.sides.straightening.preimage_closure]
  change R.sides.straightening ⁻¹' closure {z : ℂ | z.im < 0} = _
  rw [Complex.closure_setOfPred_im_lt]
  ext z
  change (R.sides.straightening z).im ≤ 0 ↔
    0 ≤ (starRingEnd ℂ (R.sides.straightening z)).im
  simp only [Complex.conj_im, neg_nonneg]

/-- Genuine new boundary-chart interpretation for the actual νQ. -/
theorem boundary_turn (R : PointFullLinePreparationStep a y P line ν α) :
    ∀ p ∈ frontier R.Q, ∃ C : PointRetainedConeNeighborhood a y R.Q p,
      R.νQ p = Real.pi - C.flatPhysicalWidth := by
  intro p hp
  obtain ⟨s, hs⟩ := (R.frontier_eq ▸ hp :
    p ∈ range (fun r ↦ (R.strip (fullStripTop R.height_pos.le r)).1))
  subst p
  obtain ⟨E, _, hturn, _⟩ := R.top_retained s
  exact ⟨E, (R.νQ_representation.boundary_eq _ hp).trans hturn.symm⟩

/-- No mass estimate is used in place of ambient equality: all finite
coefficient masses and positive/negative parts are literally unchanged. -/
theorem conserved_finite_data (R : PointFullLinePreparationStep a y P line ν α) :
    pointSignedCurvatureMass R.νQ α = pointSignedCurvatureMass ν α ∧
    pointSignedBudgetMass R.νQ α = pointSignedBudgetMass ν α ∧
    pointSignedPositivePart R.νQ = pointSignedPositivePart ν ∧
    pointSignedNegativePart R.νQ = pointSignedNegativePart ν ∧
    pointSignedPositiveMass R.νQ α = pointSignedPositiveMass ν α ∧
    pointSignedNegativeMass R.νQ α = pointSignedNegativeMass ν α ∧
    pointSignedSurplusMass R.νQ α = pointSignedSurplusMass ν α := by
  rw [R.curvature_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PointFullLinePreparationStep

end RepulsiveCoulomb
