import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudgetEquality
import LeanResearch.RepulsiveCoulomb.PointRetainedApexBudgetTransport

/-! SOURCE-ONLY, UNCOMPILED. General ambient finite-coefficient algebra for
Pro's disappearing-apex cut. No original-atom or initial-line support is used.
Geometry must identify this coefficient function after constructing the cut. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def disappearingApexCurvature (ν : ℂ →₀ ℝ) (p z : ℂ) : ℂ →₀ ℝ :=
  ν - Finsupp.single p (ν p) + Finsupp.single z Real.pi

@[simp] theorem disappearingApexCurvature_at_apex (ν : ℂ →₀ ℝ)
    {p z : ℂ} (hz : z ≠ p) : disappearingApexCurvature ν p z p = 0 := by
  simp [disappearingApexCurvature,hz,Ne.symm hz]

@[simp] theorem disappearingApexCurvature_at_departure (ν : ℂ →₀ ℝ)
    {p z : ℂ} (hz : z ≠ p) : disappearingApexCurvature ν p z z = ν z+Real.pi := by
  simp [disappearingApexCurvature,hz,Ne.symm hz]

theorem disappearingApexCurvature_off (ν : ℂ →₀ ℝ) {p z x : ℂ}
    (hxp : x ≠ p) (hxz : x ≠ z) : disappearingApexCurvature ν p z x = ν x := by
  simp [disappearingApexCurvature,hxp,hxz,Ne.symm hxp,Ne.symm hxz]

/-- Every equality in Pro (caseII-equalities) follows from the original
invariant. In particular the residual budget is literally the OLD negative
part, even when the departure z later becomes a positive-turn vertex. -/
theorem PointSignedBudgetInvariant.disappearingApex_equalities
    {ν α : ℂ →₀ ℝ} (h : PointSignedBudgetInvariant ν α) (p : ℂ) {β : ℝ}
    (hboundary : ν p = Real.pi-β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α p) :
    α p = β ∧ 0 ≤ ν p ∧
      pointSignedPositiveMassAway ν α p = 0 ∧
      (∀ x, x ≠ p → ν x ≤ 0) ∧
      (∀ x, x ≠ p → α x = signedBudgetNeg (ν x)) ∧
      retainedApexBudget α p β = pointSignedNegativePart ν := by
  obtain ⟨hα,hν,hpos,haway,hoff⟩ := h.full_angle_equality p hboundary hβπ hβα
  refine ⟨hα,hpos,haway,h.full_angle_off_apex_nonpositive p hboundary hβπ hβα,
    hoff,?_⟩
  unfold retainedApexBudget
  rw [h.full_angle_surplus_single p hboundary hβπ hβα]
  abel

/-- Thus there are no budget-only marks away from the disappearing apex. -/
theorem PointSignedBudgetInvariant.disappearingApex_marked_iff_negative
    {ν α : ℂ →₀ ℝ} (h : PointSignedBudgetInvariant ν α) (p : ℂ) {β : ℝ}
    (hboundary : ν p = Real.pi-β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α p)
    {x : ℂ} (hxp : x ≠ p) :
    x ∈ pointSignedMarked ν α ↔ ν x < 0 := by
  obtain ⟨_,_,_,hnonpos,hoff,_⟩ := h.disappearingApex_equalities p hboundary hβπ hβα
  rw [mem_pointSignedMarked,hoff x hxp]
  have hn := hnonpos x hxp
  constructor
  · rintro (hne | hne)
    · exact lt_of_le_of_ne hn hne
    · by_contra hnot
      have hz : ν x = 0 := le_antisymm hn (le_of_not_gt hnot)
      exact hne (by simp [hz])
  · intro hx
    exact Or.inl hx.ne

/-- Positive additions at z cannot enlarge a negative coefficient. This
requires NO inequality pi <= alpha(z). -/
theorem disappearingApex_negative_part_add_pi (r : ℝ) :
    signedBudgetNeg (r+Real.pi) ≤ signedBudgetNeg r := by
  apply max_le
  · exact (show -(r+Real.pi) ≤ -r by linarith [Real.pi_pos]).trans (le_max_left _ _)
  · exact signedBudgetNeg_nonneg r

theorem PointSignedBudgetInvariant.disappearingApex_dominates
    {ν α : ℂ →₀ ℝ} (h : PointSignedBudgetInvariant ν α) (p : ℂ) {z : ℂ} (hz : z ≠ p)
    {β : ℝ} (hboundary : ν p = Real.pi-β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α p) :
    ∀ x, signedBudgetNeg (disappearingApexCurvature ν p z x) ≤ retainedApexBudget α p β x := by
  obtain ⟨hα,_,_,_,hoff,_⟩ := h.disappearingApex_equalities p hboundary hβπ hβα
  intro x
  by_cases hxp : x = p
  · subst x
    simp [disappearingApexCurvature_at_apex ν hz,retainedApexBudget_at,hα]
  · rw [retainedApexBudget_off α β hxp,hoff x hxp]
    by_cases hxz : x = z
    · subst x
      rw [disappearingApexCurvature_at_departure ν hz]
      exact disappearingApex_negative_part_add_pi _
    · rw [disappearingApexCurvature_off ν hxp hxz]

private theorem disappearingApex_add_mass (ν α : ℂ →₀ ℝ) (p : ℂ) (r : ℝ) :
    pointSignedCurvatureMass (retainedApexCurvature ν p r) α =
      pointSignedCurvatureMass ν α+r := by
  have hm := (retainedApex_mass_changes ν α p r).1
  simpa only [pointSignedCurvatureMass_eq_support_sum] using hm

/-- Separate exact mass changes; the domain of the finite coefficient is the
ambient plane, so disappearance does not hide a missing atom in notation. -/
theorem disappearingApex_mass_changes (ν α : ℂ →₀ ℝ) (p z : ℂ) {β : ℝ}
    (hboundary : ν p = Real.pi-β) :
    pointSignedCurvatureMass (disappearingApexCurvature ν p z) (retainedApexBudget α p β) =
      pointSignedCurvatureMass ν α+β ∧
    pointSignedBudgetMass (disappearingApexCurvature ν p z) (retainedApexBudget α p β) =
      pointSignedBudgetMass ν α-β := by
  have he : disappearingApexCurvature ν p z =
      retainedApexCurvature (retainedApexCurvature ν p (-ν p)) z Real.pi := by
    ext x
    simp only [disappearingApexCurvature,retainedApexCurvature,Finsupp.add_apply,
      Finsupp.sub_apply,Finsupp.single_neg,Finsupp.neg_apply]
    ring
  have hmass1 := disappearingApex_add_mass ν α p (-ν p)
  have hmass2 := disappearingApex_add_mass (retainedApexCurvature ν p (-ν p)) α z Real.pi
  have hA := (retainedApex_mass_changes ν α p β).2
  constructor
  · have hm : pointSignedCurvatureMass (disappearingApexCurvature ν p z) α =
        pointSignedCurvatureMass ν α+β := by
      rw [he,hmass2,hmass1,hboundary]
      ring
    simpa only [pointSignedCurvatureMass_eq_support_sum] using hm
  · simpa only [pointSignedBudgetMass_eq_support_sum] using hA

theorem PointSignedBudgetInvariant.disappearingApex
    {ν α : ℂ →₀ ℝ} (h : PointSignedBudgetInvariant ν α) (p : ℂ) {z : ℂ} (hz : z ≠ p)
    {β : ℝ} (hboundary : ν p = Real.pi-β) (hβπ : β ≤ Real.pi) (hβα : β ≤ α p)
    (hremaining : 0 < pointSignedBudgetMass ν α-β) :
    PointSignedBudgetInvariant (disappearingApexCurvature ν p z) (retainedApexBudget α p β) := by
  obtain ⟨hV,hA⟩ := disappearingApex_mass_changes ν α p z hboundary
  refine ⟨h.disappearingApex_dominates p hz hboundary hβπ hβα,?_,?_⟩
  · rwa [hA]
  · rw [hA,hV]
    have hm := h.mass_le
    linarith

/-- Conditional support transport after the literal residual identity has
been CONSTRUCTED. Cleanliness is needed only away from the fully spent apex. -/
theorem disappearingApex_budget_support_retained {P Q S T : Set ℂ}
    {α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ} (hαp : α p = β)
    (hQ : Q = P \ (S \ T))
    (hbudgetP : ∀ x, α x ≠ 0 → x ∈ P)
    (hclean : ∀ x ∈ S \ T, x ≠ p → α x = 0) :
    ∀ x, retainedApexBudget α p β x ≠ 0 → x ∈ Q := by
  intro x hx
  have hxp : x ≠ p := by
    intro he
    subst x
    exact hx (by simp [retainedApexBudget_at,hαp])
  have hαx : α x ≠ 0 := by rwa [retainedApexBudget_off α β hxp] at hx
  rw [hQ]
  exact ⟨hbudgetP x hαx,fun hw ↦ hαx (hclean x hw hxp)⟩

end RepulsiveCoulomb
