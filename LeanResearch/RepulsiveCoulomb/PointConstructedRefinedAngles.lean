import LeanResearch.RepulsiveCoulomb.FiniteLinkComplementTargetCover

/-! SOURCE-ONLY, UNCOMPILED. Instantiate the refined disk cover and all short
positive widths from actual incident geometry and pointwise budget balance.
The common incident source patches and direction data are retained verbatim. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The constructed finite subdivision is ready for physical branch maps.
Both angular covers, positivity, shortness and angle conservation are outputs.
The theorem does not assume or construct the final glued atlas. -/
theorem exists_point_constructed_refined_angles
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y)) (p : ℂ)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
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
          ∃ Q : FiniteLinkComplementRefinement u owner (coalescedPointExponent a y p / 2 + 1),
            (∀ x : (Σ j : Fin N, Fin (Q.count j)),
              0 < refinedIncidentTargetWidth Q width x.1 x.2 ∧
                refinedIncidentTargetWidth Q width x.1 x.2 ≤ Real.pi) ∧
            (∑ x : (Σ j : Fin N, Fin (Q.count j)),
              refinedIncidentTargetWidth Q width x.1 x.2) = 2 * Real.pi ∧
            (∀ R : ℝ, ∀ z : ℂ, ‖z‖ ≤ R → ∃ x : (Σ j : Fin N, Fin (Q.count j)),
              z ∈ flatLinkOccupiedDisk R (Q.node x.1 x.2.castSucc) (Q.node x.1 x.2.succ)) ∧
            (∀ R : ℝ, ∀ z : ℂ, ‖z‖ ≤ R → ∃ x : (Σ j : Fin N, Fin (Q.count j)),
              z ∈ flatLinkOccupiedDisk R
                (refinedIncidentTargetNode Q width x.1 x.2.castSucc)
                (refinedIncidentTargetNode Q width x.1 x.2.succ)) := by
  classical
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  obtain ⟨N, hN, u, hu, hu0, huT, owner, howner, width, hwpos, hwtotal, hwowned, hwcomp, _⟩ :=
    exists_point_constructed_incident_angles ha y L p hc hbalance P C hdis hρ hρP hρC lo forward hpolar i₀
  obtain ⟨Q⟩ := exists_finiteLink_complement_refinement u hu owner hk
  have howned : ∀ j, j ∈ range owner → width j ≤ Real.pi := by
    rintro j ⟨i, rfl⟩
    rw [hwowned i]
    split_ifs
    · have hβ := (L.get i.1).positive
      have hβπ := (L.get i.1).le_pi
      nlinarith
    · exact le_rfl
  refine ⟨N, hN, u, hu, hu0, huT, owner, howner, width, hwpos, hwtotal, hwowned, hwcomp, Q,
    (fun x ↦ ⟨refinedIncidentTargetWidth_pos Q hk width hwpos x.1 x.2,
      refinedIncidentTargetWidth_le_pi Q width howned x.1 x.2⟩), ?_, ?_, ?_⟩
  · exact (refinedIncidentTargetWidth_total Q width hwcomp).trans hwtotal
  · exact fun R z hz ↦ finiteLinkComplementRefinement_whole_source_cover hN hu0 huT Q R hz
  · exact fun R z hz ↦ refinedIncidentTargetWedges_cover hN Q width hwcomp hwtotal R hz

end RepulsiveCoulomb
