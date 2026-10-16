import Mathlib.Analysis.Complex.AbsMax

/-! A bounded planar region lies in any closed ball containing its frontier.
Uses Mathlib's maximum modulus principle applied to the affine map z ↦ z-c. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem planar_closure_subset_closedBall_of_frontier {U : Set ℂ}
    (hU : Bornology.IsBounded U) (c : ℂ) (R : ℝ)
    (hfront : frontier U ⊆ closedBall c R) : closure U ⊆ closedBall c R := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm]
  apply Complex.norm_le_of_forall_mem_frontier_norm_le hU
    ((differentiable_id.sub_const c).diffContOnCl)
    (fun w hw => ?_) hz
  simpa only [mem_closedBall, dist_eq_norm, id_eq] using hfront hw

end RepulsiveCoulomb
