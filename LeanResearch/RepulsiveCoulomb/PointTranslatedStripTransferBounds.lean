import LeanResearch.RepulsiveCoulomb.BoundaryPreparationRankDraft
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! NEW SOURCE-ONLY, UNCOMPILED. Narrow algebra after the ACTUAL geometry has
identified the ambient Finsupp transfer. These lemmas assert no geometric move. -/
noncomputable section
namespace RepulsiveCoulomb

theorem pointTranslatedTransfer_negative_nonincrease (ν : ℂ→₀ℝ)
    {p z : ℂ} (hpz : p≠z) (hp : 0≤ν p) :
    ∀ x,pointSignedNegativePart (BoundaryPreparation.transfer ν p z) x≤
      pointSignedNegativePart ν x := by
  intro x
  by_cases hxp : x=p
  · subst x
    rw [pointSignedNegativePart_apply,BoundaryPreparation.transfer_source ν hpz,signedBudgetNeg_zero]
    exact signedBudgetNeg_nonneg _
  · by_cases hxz : x=z
    · subst x
      rw [pointSignedNegativePart_apply,pointSignedNegativePart_apply,
        BoundaryPreparation.transfer_target ν hpz]
      unfold signedBudgetNeg
      exact max_le_max (by linarith) le_rfl
    · rw [pointSignedNegativePart_apply,pointSignedNegativePart_apply,
        BoundaryPreparation.transfer_away ν hxp hxz]

theorem pointTranslatedTransfer_curvature_mass (ν α : ℂ→₀ℝ) (p z : ℂ) :
    pointSignedCurvatureMass (BoundaryPreparation.transfer ν p z) α=
      pointSignedCurvatureMass ν α := by
  classical
  rw [pointSignedCurvatureMass_eq_support_sum,pointSignedCurvatureMass_eq_support_sum]
  change (BoundaryPreparation.transfer ν p z).sum (fun _ r ↦ r)=ν.sum (fun _ r ↦ r)
  unfold BoundaryPreparation.transfer
  rw [Finsupp.sum_sub_index (fun _ _ _ ↦ rfl),
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  simp

end RepulsiveCoulomb
