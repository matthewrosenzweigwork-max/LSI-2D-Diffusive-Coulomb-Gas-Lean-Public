import LeanResearch.RepulsiveCoulomb.PointIncidentNormalizedCells
import LeanResearch.RepulsiveCoulomb.PointNoIncidentBudgetFlatness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Pairwise

/-! SOURCE-ONLY, UNCOMPILED. Debit each actual own-apex sector exactly once
through its constructed cell ownership. Passing sectors contribute pi and
unowned cells retain their physical angle. The total is proved from the
literal finite allocated budget and the original pointwise balance. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def pointIncidentApexCharge {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (p : ℂ) (S : PointActualAllocatedSector a y) : ℝ :=
  if p = S.apex then S.beta else 0

theorem pointActualAllocatedBudget_eq_sum_get
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) :
    pointActualAllocatedBudget L p = ∑ i : Fin L.length, pointIncidentApexCharge p (L.get i) := by
  classical
  have hlist : pointActualAllocatedBudget L p = (L.map (pointIncidentApexCharge p)).sum := by
    induction L with
    | nil => simp [pointActualAllocatedBudget]
    | cons S L ih =>
        simp only [pointActualAllocatedBudget, List.foldr_cons, Finsupp.add_apply,
          List.map_cons, List.sum_cons]
        rw [show (L.foldr (fun (S : PointActualAllocatedSector a y) (b : ℂ →₀ ℝ) ↦
            Finsupp.single S.apex S.beta + b) 0) p =
          (L.map (pointIncidentApexCharge p)).sum from ih]
        simp [pointIncidentApexCharge, Finsupp.single_apply, eq_comm]
  rw [hlist]
  simpa only [List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem L (pointIncidentApexCharge p)).symm

/-- Incident indices retain occurrences of the actual finite sector list.
No deduplication of apices or sectors can silently lose an allocation. -/
def PointIncidentIndex {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) :=
  {i : Fin L.length // p ∈ range (L.get i).map}

instance {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) : Fintype (PointIncidentIndex L p) := by
  classical
  unfold PointIncidentIndex
  infer_instance

/-- The geometric separation premise for actual incident indices follows from
the constructed prefix's listwise disjoint interiors and closed-range lemma. -/
theorem PointFiniteActualCutPrefix.incident_closed_disjoint
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {V : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y V ν α}
    (T : PointFiniteActualCutPrefix a y K) (p : ℂ)
    (i j : PointIncidentIndex T.sectors p) (hij : i ≠ j) :
    Disjoint (range (T.sectors.get i.1).map) (T.sectors.get j.1).openImage := by
  have hne : i.1 ≠ j.1 := fun he ↦ hij (Subtype.ext he)
  have hdis : Disjoint (T.sectors.get i.1).openImage (T.sectors.get j.1).openImage := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact T.pairwise_disjoint_openImages.rel_get_of_lt h
    · exact (T.pairwise_disjoint_openImages.rel_get_of_lt h).symm
  exact T.closed_range_disjoint_openImage ha y _ _ (List.get_mem T.sectors j.1) hdis

theorem pointActualAllocatedBudget_eq_incident_sum
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) :
    pointActualAllocatedBudget L p =
      ∑ i : PointIncidentIndex L p, pointIncidentApexCharge p (L.get i.1) := by
  classical
  rw [pointActualAllocatedBudget_eq_sum_get]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin L.length ↦ p ∈ range (L.get i).map)
    (fun i : Fin L.length ↦ pointIncidentApexCharge p (L.get i))
  have hz : (∑ i : {i : Fin L.length // p ∉ range (L.get i).map},
      pointIncidentApexCharge p (L.get i.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply if_neg
    intro he
    apply i.2
    exact ⟨flatLinkSectorApex (L.get i.1).positive.le, he.symm⟩
  rw [hz, add_zero] at hs
  exact hs.symm

theorem finiteLink_cell_width_sum {N : ℕ} (u : Fin (N + 1) → ℝ) :
    (∑ j : Fin N, (u j.succ - u j.castSucc)) = u (Fin.last N) - u 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ u
  have hlast := Fin.sum_univ_castSucc u
  linarith

def incidentCellTargetWidth
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ι : Type*} [Fintype ι] {N : ℕ}
    (S : ι → PointActualAllocatedSector a y) (p : ℂ) (k c : ℝ)
    (u : Fin (N + 1) → ℝ) (owner : ι ↪ Fin N) (j : Fin N) : ℝ :=
  k * (u j.succ - u j.castSucc) -
    (1 - c) * ∑ i, if owner i = j then pointIncidentApexCharge p (S i) else 0

theorem incidentCellTargetWidth_owned
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ι : Type*} [Fintype ι] {N : ℕ}
    (S : ι → PointActualAllocatedSector a y) (p : ℂ) (k c : ℝ)
    (u : Fin (N + 1) → ℝ) (owner : ι ↪ Fin N) (i : ι) :
    incidentCellTargetWidth S p k c u owner (owner i) =
      k * (u (owner i).succ - u (owner i).castSucc) -
        (1 - c) * pointIncidentApexCharge p (S i) := by
  classical
  simp only [incidentCellTargetWidth, owner.injective.eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem incidentCellTargetWidth_unowned
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ι : Type*} [Fintype ι] {N : ℕ}
    (S : ι → PointActualAllocatedSector a y) (p : ℂ) (k c : ℝ)
    (u : Fin (N + 1) → ℝ) (owner : ι ↪ Fin N) (j : Fin N) (hj : j ∉ range owner) :
    incidentCellTargetWidth S p k c u owner j = k * (u j.succ - u j.castSucc) := by
  classical
  have hz : ∀ i, owner i ≠ j := fun i he ↦ hj ⟨i, he⟩
  simp [incidentCellTargetWidth, hz]

/-- Actual occupied widths: c*beta at the sector's own apex, and pi at a
passing edge. In particular the passing angle is never changed to c*pi. -/
theorem incidentCellTargetWidth_actual_piece
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ι : Type*} [Fintype ι] {N : ℕ}
    (S : ι → PointActualAllocatedSector a y) (p : ℂ)
    (P : ∀ i, PointIncidentSectorSourcePatch (S i) p)
    {k : ℝ} (hk : 0 < k) (c : ℝ) (u : Fin (N + 1) → ℝ) (owner : ι ↪ Fin N)
    (hwidth : ∀ i, u (owner i).succ - u (owner i).castSucc = (P i).angle / k) (i : ι) :
    incidentCellTargetWidth S p k c u owner (owner i) =
      if p = (S i).apex then c * (S i).beta else Real.pi := by
  classical
  rw [incidentCellTargetWidth_owned, hwidth i, mul_div_cancel₀ _ hk.ne', (P i).angle_eq]
  by_cases he : p = (S i).apex
  · simp only [pointIncidentApexCharge, if_pos he]
    ring
  · simp [pointIncidentApexCharge, he]

theorem incidentCellTargetWidth_pos
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ι : Type*} [Fintype ι] {N : ℕ}
    (S : ι → PointActualAllocatedSector a y) (p : ℂ)
    (P : ∀ i, PointIncidentSectorSourcePatch (S i) p)
    {k c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (u : Fin (N + 1) → ℝ) (hu : StrictMono u) (owner : ι ↪ Fin N)
    (hwidth : ∀ i, u (owner i).succ - u (owner i).castSucc = (P i).angle / k) :
    ∀ j, 0 < incidentCellTargetWidth S p k c u owner j := by
  classical
  intro j
  by_cases hj : j ∈ range owner
  · obtain ⟨i, rfl⟩ := hj
    rw [incidentCellTargetWidth_actual_piece S p P hk c u owner hwidth]
    split_ifs
    · exact mul_pos hc (S i).positive
    · exact Real.pi_pos
  · rw [incidentCellTargetWidth_unowned S p k c u owner j hj]
    exact mul_pos hk (sub_pos.mpr (hu (show j.castSucc < j.succ from Fin.castSucc_lt_succ)))

/-- All old physical cell widths telescope once, and each apex debit occurs
once because its whole occupied sector owns exactly one cell. -/
theorem incidentCellTargetWidth_sum
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {ι : Type*} [Fintype ι] {N : ℕ}
    (S : ι → PointActualAllocatedSector a y) (p : ℂ) (k c : ℝ)
    (u : Fin (N + 1) → ℝ) (owner : ι ↪ Fin N) :
    (∑ j, incidentCellTargetWidth S p k c u owner j) =
      k * (u (Fin.last N) - u 0) - (1 - c) * ∑ i, pointIncidentApexCharge p (S i) := by
  classical
  unfold incidentCellTargetWidth
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    finiteLink_cell_width_sum, Finset.sum_comm]
  simp

/-- The actual pointwise balance yields the target full angle. Neither a
2*pi target sum nor a final atlas is an input. Nonincident list entries are
removed only after proving their literal apex charges vanish. -/
theorem pointIncidentCellTargetWidth_sum_eq_two_pi
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) (c : ℝ)
    (hbalance : (1 - c) * pointActualAllocatedBudget L p =
      Real.pi * coalescedPointExponent a y p)
    {N : ℕ} (u : Fin (N + 1) → ℝ) (hu0 : u 0 = 0)
    (huT : u (Fin.last N) = 2 * Real.pi) (owner : PointIncidentIndex L p ↪ Fin N) :
    (∑ j, incidentCellTargetWidth (fun i : PointIncidentIndex L p ↦ L.get i.1)
      p (coalescedPointExponent a y p / 2 + 1) c u owner j) = 2 * Real.pi := by
  rw [incidentCellTargetWidth_sum, hu0, huT, sub_zero,
    ← pointActualAllocatedBudget_eq_incident_sum, hbalance]
  ring

end RepulsiveCoulomb
