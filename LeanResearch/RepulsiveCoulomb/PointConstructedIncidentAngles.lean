import LeanResearch.RepulsiveCoulomb.PointIncidentCellAngleBalance

/-! SOURCE-ONLY, UNCOMPILED. End-to-end join of the actual incident geometry,
constructed cell ownership, literal list budget, positive target widths and
ordered target disk cover. Target-angle conservation is an output. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def finiteLinkWidthSequence {N : ℕ} (width : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j < N then width ⟨j, hj⟩ else 0

theorem finiteLinkWidthSequence_total {N : ℕ} (width : Fin N → ℝ) :
    linkCumulativeWidth (finiteLinkWidthSequence width) N = ∑ j, width j := by
  classical
  rw [linkCumulativeWidth, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [finiteLinkWidthSequence, i.2]

theorem finiteLinkWidthSequence_pos {N : ℕ} (width : Fin N → ℝ)
    (hw : ∀ j, 0 < width j) : ∀ j < N, 0 < finiteLinkWidthSequence width j := by
  intro j hj
  simpa [finiteLinkWidthSequence, hj] using hw ⟨j, hj⟩

/-- Actual incident patches determine all ordered cells and all positive new
widths. The resulting disk cover is constructed, with no atlas, target cover,
cyclic ordering, or 2*pi target total among the hypotheses. -/
theorem exists_point_constructed_incident_angles
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) {c : ℝ} (hc : 0 < c)
    (hbalance : (1 - c) * pointActualAllocatedBudget L p =
      Real.pi * coalescedPointExponent a y p)
    (P : ∀ i : PointIncidentIndex L p, PointIncidentSectorSourcePatch (L.get i.1) p)
    (C : PointFlatLinkConeDisk a y p)
    (hdis : ∀ i j : PointIncidentIndex L p, i ≠ j →
      Disjoint (range (L.get i.1).map) (L.get j.1).openImage)
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ∀ i, ρ ≤ (P i).radius) (hρC : ρ ≤ C.radius)
    (lo : PointIncidentIndex L p → ℝ) (forward : PointIncidentIndex L p → Bool)
    (hpolar : ∀ i, (P i).PolarAt C (hρP i) (lo i) (forward i))
    (i₀ : PointIncidentIndex L p) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Fin (N + 1) → ℝ,
      StrictMono u ∧ u 0 = 0 ∧ u (Fin.last N) = 2 * Real.pi ∧
      ∃ owner : PointIncidentIndex L p ↪ Fin N,
        (∀ i, u (owner i).castSucc = normalizedIncidentLower (lo i₀) (lo i) ∧
          u (owner i).succ = normalizedIncidentLower (lo i₀) (lo i) +
            (P i).angle / (coalescedPointExponent a y p / 2 + 1)) ∧
        ∃ width : Fin N → ℝ,
          (∀ j, 0 < width j) ∧ (∑ j, width j) = 2 * Real.pi ∧
          (∀ i, width (owner i) = if p = (L.get i.1).apex then c * (L.get i.1).beta else Real.pi) ∧
          (∀ j, j ∉ range owner → width j =
            (coalescedPointExponent a y p / 2 + 1) * (u j.succ - u j.castSucc)) ∧
          (∀ R : ℝ, ∀ z : ℂ, ‖z‖ ≤ R → ∃ j : Fin N,
            z ∈ flatLinkOccupiedDisk R (linkCumulativeWidth (finiteLinkWidthSequence width) j.1)
              (linkCumulativeWidth (finiteLinkWidthSequence width) (j.1 + 1))) := by
  let S : PointIncidentIndex L p → PointActualAllocatedSector a y := fun i ↦ L.get i.1
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  obtain ⟨N, hN, u, hu, hu0, huT, owner, howner⟩ :=
    exists_pointIncident_whole_cell_partition ha y S p P C hdis hρ hρP hρC lo forward hpolar i₀
  have hwidth (i : PointIncidentIndex L p) :
      u (owner i).succ - u (owner i).castSucc = (P i).angle / k := by
    rw [(howner i).1, (howner i).2]
    ring
  let width := incidentCellTargetWidth S p k c u owner
  have hwpos : ∀ j, 0 < width j := incidentCellTargetWidth_pos S p P hk hc u hu owner hwidth
  have hwtotal : (∑ j, width j) = 2 * Real.pi :=
    pointIncidentCellTargetWidth_sum_eq_two_pi L p c hbalance u hu0 huT owner
  refine ⟨N, hN, u, hu, hu0, huT, owner, howner, width, hwpos, hwtotal,
    (fun i ↦ incidentCellTargetWidth_actual_piece S p P hk c u owner hwidth i),
    (fun j hj ↦ incidentCellTargetWidth_unowned S p k c u owner j hj), ?_⟩
  intro R z hz
  apply orderedEuclideanWedges_cover hN (finiteLinkWidthSequence width) _ R hz
  rw [finiteLinkWidthSequence_total]
  exact hwtotal

end RepulsiveCoulomb
