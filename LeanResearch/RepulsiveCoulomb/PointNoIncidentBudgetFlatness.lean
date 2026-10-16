module

public import LeanResearch.RepulsiveCoulomb.PointFiniteSectorLocalGeometry

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Exact allocation rules out positive ambient
curvature at a point with no incident sector. Hence the unchanged local
piece there is genuinely Euclidean. The statement uses the actual finite
allocated-budget expression; it does not assume that the complement is flat. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointActualAllocatedBudget_apply_eq_zero_of_no_incident
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ)
    (hno : ∀ S ∈ L, p ∉ range S.map) : pointActualAllocatedBudget L p = 0 := by
  classical
  induction L with
  | nil => simp [pointActualAllocatedBudget]
  | cons S L ih =>
      have hp : p ≠ S.apex := by
        intro he
        apply hno S List.mem_cons_self
        rw [he]
        exact mem_range_self (flatLinkSectorApex S.positive.le)
      have htail : pointActualAllocatedBudget L p = 0 :=
        ih (fun E hE ↦ hno E (List.mem_cons_of_mem S hE))
      simp only [pointActualAllocatedBudget, List.foldr_cons, Finsupp.add_apply]
      rw [Finsupp.single_eq_of_ne hp]
      exact zero_add _ |>.trans htail

theorem pointExponent_eq_zero_of_exact_budget_no_incident
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) (c : ℝ)
    (hbalance : (1 - c) * pointActualAllocatedBudget L p =
      Real.pi * coalescedPointExponent a y p)
    (hno : ∀ S ∈ L, p ∉ range S.map) : coalescedPointExponent a y p = 0 := by
  rw [pointActualAllocatedBudget_apply_eq_zero_of_no_incident L p hno, mul_zero] at hbalance
  exact (mul_eq_zero.mp hbalance.symm).resolve_left Real.pi_ne_zero

/-- The previously constructed genuine cone disk is an actual Euclidean
metric disk in the no-incident branch, by exact pointwise budget balance. -/
theorem PointFlatLinkConeDisk.metric_of_exact_budget_no_incident
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) (c : ℝ)
    (hbalance : (1 - c) * pointActualAllocatedBudget L p =
      Real.pi * coalescedPointExponent a y p)
    (hno : ∀ S ∈ L, p ∉ range S.map) (C : PointFlatLinkConeDisk a y p)
    (z w : ℂ)
    (hz : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hw : (pointSmoothConformalEDist a y w p).toReal ≤ C.radius) :
    (pointSmoothConformalEDist a y z w).toReal = dist (C.chart z) (C.chart w) := by
  rw [C.metric z hz w hw, pointClassicalConeDist_eq_euclidean_of_zero y
    (pointExponent_eq_zero_of_exact_budget_no_incident L p c hbalance hno)]

end RepulsiveCoulomb
