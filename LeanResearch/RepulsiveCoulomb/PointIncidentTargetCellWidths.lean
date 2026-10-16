import LeanResearch.RepulsiveCoulomb.PointConstructedIncidentSurgeryChart

/-! SOURCE-ONLY, UNCOMPILED. Recover strict positive short target widths
from the actual retained chart data. These geometric bounds are conclusions,
not additional fields or hypotheses for the overlap proof. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
namespace PointConstructedIncidentSurgeryChart
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}
    {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

theorem target_cell_width_bounds
    (D : PointConstructedIncidentSurgeryChart ha L p c hc hc1)
    (x : Σ j : Fin D.N, Fin (D.refinement.count j)) :
    0 < refinedIncidentTargetNode D.refinement D.width x.1 x.2.succ -
      refinedIncidentTargetNode D.refinement D.width x.1 x.2.castSucc ∧
    refinedIncidentTargetNode D.refinement D.width x.1 x.2.succ -
      refinedIncidentTargetNode D.refinement D.width x.1 x.2.castSucc ≤ Real.pi := by
  rw [refinedIncidentTargetNode_step]
  have hk : 0 < coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  refine ⟨refinedIncidentTargetWidth_pos D.refinement hk D.width D.width_pos x.1 x.2,
    refinedIncidentTargetWidth_le_pi D.refinement D.width ?_ x.1 x.2⟩
  rintro j ⟨i, rfl⟩
  rw [D.width_owned i]
  exact (D.data.paired i).new.angle_le_pi

end PointConstructedIncidentSurgeryChart
end RepulsiveCoulomb
