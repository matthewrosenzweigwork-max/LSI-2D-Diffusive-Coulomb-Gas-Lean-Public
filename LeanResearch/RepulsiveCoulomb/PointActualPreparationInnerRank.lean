import LeanResearch.RepulsiveCoulomb.PointOriginalMaximalTranslatedMove
import LeanResearch.RepulsiveCoulomb.PointActualUnmarkedPreparationState

/-! SOURCE-ONLY, UNCOMPILED. The actual translated move strictly decreases
the common-mark rank n+i. Here n counts supp(nu) UNION supp(alpha), including
budget-only marks. The old curvature-only rank helper is not silently reused
with a different meaning. All descent facts below are derived from the actual
Finsupp transfer, literal residual, and attained top contact. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def pointPreparationInnerRank (P : Set ℂ) (ν α : ℂ →₀ ℝ) : ℕ :=
  (pointSignedMarked ν α).card + (pointCutInteriorMarks P ν α).card

theorem pointPreparationInnerRank_le_twice_marked (P : Set ℂ) (ν α : ℂ →₀ ℝ) :
    pointPreparationInnerRank P ν α ≤ 2 * (pointSignedMarked ν α).card := by
  classical
  have hi : (pointCutInteriorMarks P ν α).card ≤ (pointSignedMarked ν α).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  unfold pointPreparationInnerRank
  omega

namespace PointConstructedTranslatedMove
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ}
  (M : PointConstructedTranslatedMove a y ha P ν α)

/-- Positive turn is the actual transported amount pi minus the constructed
old corner width; it is not a rank-certificate field. -/
theorem source_positive : 0 < ν M.limit.cutApex := by
  rw [M.residual.transfer_amount]
  exact sub_pos.mpr M.data.angle_lt_pi

/-- Allocation is unchanged and supported in the literal residual, whereas
the old apex is removed. Thus its old allocation is zero. -/
theorem source_budget_zero : α M.limit.cutApex = 0 := by
  by_contra h
  exact M.residual.apex_removed (M.next.allocation_support _ h)

theorem source_marked : M.limit.cutApex ∈ pointSignedMarked ν α :=
  (mem_pointSignedMarked ν α _).mpr (Or.inl M.source_positive.ne')

/-- Both changed points are on the old frontier. Every new interior point is
old interior, so its actual curvature coefficient is unchanged. -/
theorem interior_unchanged :
    ∀ x ∈ interior M.limit.cutRegion, M.limit.cutCurvature x = ν x := by
  intro x hx
  have hi := interior_mono M.residual.subset_old hx
  exact BoundaryPreparation.transfer_away ν
    (fun he ↦ M.residual.apex_old_frontier.2 (he ▸ hi))
    (fun he ↦ M.residual.origin_old_frontier.2 (he ▸ hi))

theorem interior_marks_subset :
    pointCutInteriorMarks M.limit.cutRegion M.limit.cutCurvature α ⊆
      pointCutInteriorMarks P ν α :=
  pointCutInteriorMarks_subset M.residual.subset_old M.interior_unchanged (fun _ _ ↦ rfl)

theorem interior_mark_card_le :
    (pointCutInteriorMarks M.limit.cutRegion M.limit.cutCurvature α).card ≤
      (pointCutInteriorMarks P ν α).card :=
  Finset.card_le_card M.interior_marks_subset

/-- Exact transfer can add only z, and p is no longer marked in either
coefficient. Target cancellation is allowed by this inclusion. -/
theorem marked_subset_insert_erase :
    pointSignedMarked M.limit.cutCurvature α ⊆
      insert (M.limit.cutRay 0) ((pointSignedMarked ν α).erase M.limit.cutApex) := by
  classical
  intro x hx
  have hxp : x ≠ M.limit.cutApex := by
    intro he
    subst x
    rcases (mem_pointSignedMarked M.limit.cutCurvature α _).mp hx with hν | hα
    · exact hν (BoundaryPreparation.transfer_source ν M.residual.apex_ne_origin)
    · exact hα M.source_budget_zero
  by_cases hxz : x = M.limit.cutRay 0
  · exact Finset.mem_insert.mpr (Or.inl hxz)
  · apply Finset.mem_insert.mpr
    right
    apply Finset.mem_erase.mpr
    refine ⟨hxp, ?_⟩
    apply (mem_pointSignedMarked ν α x).mpr
    have he : M.limit.cutCurvature x = ν x :=
      BoundaryPreparation.transfer_away ν hxp hxz
    simpa only [he] using (mem_pointSignedMarked M.limit.cutCurvature α x).mp hx

theorem marked_card_le :
    (pointSignedMarked M.limit.cutCurvature α).card ≤ (pointSignedMarked ν α).card := by
  classical
  calc
    (pointSignedMarked M.limit.cutCurvature α).card ≤
        (insert (M.limit.cutRay 0) ((pointSignedMarked ν α).erase M.limit.cutApex)).card :=
      Finset.card_le_card M.marked_subset_insert_erase
    _ ≤ ((pointSignedMarked ν α).erase M.limit.cutApex).card + 1 :=
      Finset.card_insert_le _ _
    _ = (pointSignedMarked ν α).card := Finset.card_erase_add_one M.source_marked

theorem marked_card_lt_of_origin_marked
    (hz : M.limit.cutRay 0 ∈ pointSignedMarked ν α) :
    (pointSignedMarked M.limit.cutCurvature α).card < (pointSignedMarked ν α).card := by
  classical
  have hz' : M.limit.cutRay 0 ∈ (pointSignedMarked ν α).erase M.limit.cutApex :=
    Finset.mem_erase.mpr ⟨M.residual.apex_ne_origin.symm, hz⟩
  have hsub : pointSignedMarked M.limit.cutCurvature α ⊆
      (pointSignedMarked ν α).erase M.limit.cutApex := by
    simpa only [Finset.insert_eq_of_mem hz'] using M.marked_subset_insert_erase
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem M.source_marked)

/-- At a positive top clock the exact old contact and source-side separation
have already proved old interior membership in the actual residual producer.
The point is now on the new frontier, including if it is budget-only. -/
theorem interior_mark_card_lt_of_positive_contact {r : NNReal}
    (hr : 0 < r) (hm : M.limit.cutRay r ∈ pointSignedMarked ν α) :
    (pointCutInteriorMarks M.limit.cutRegion M.limit.cutCurvature α).card <
      (pointCutInteriorMarks P ν α).card :=
  pointCutInteriorMarks_card_lt_of_exposed M.residual.subset_old
    M.interior_unchanged (fun _ _ ↦ rfl) hm
    (M.residual.open_top_old_interior r hr)
    (M.residual.top_frontier (mem_range_self r))

/-- Every attained maximal translated move decreases n+i. If the contact is
z, n drops; if its clock is positive, i drops. No clean-tail hypothesis or
assumed move/rank/termination certificate appears. -/
theorem inner_rank_lt :
    pointPreparationInnerRank M.limit.cutRegion M.limit.cutCurvature α <
      pointPreparationInnerRank P ν α := by
  obtain ⟨r, hm, _⟩ := M.attained
  by_cases hr : r = 0
  · have hn := M.marked_card_lt_of_origin_marked (hr ▸ hm)
    have hi := M.interior_mark_card_le
    unfold pointPreparationInnerRank
    omega
  · have hrpos : 0 < r := lt_of_le_of_ne (show (0 : NNReal) ≤ r from r.2) (Ne.symm hr)
    have hn := M.marked_card_le
    have hi := M.interior_mark_card_lt_of_positive_contact hrpos hm
    unfold pointPreparationInnerRank
    omega

theorem outer_rank_le :
    pointCutOuterRank M.limit.cutRegion M.limit.cutCurvature α ≤ pointCutOuterRank P ν α :=
  pointCutOuterRank_le_of_preparation_coefficients M.residual.subset_old M.interior_unchanged

end PointConstructedTranslatedMove
end RepulsiveCoulomb
