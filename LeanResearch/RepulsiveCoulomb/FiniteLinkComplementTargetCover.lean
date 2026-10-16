module

public import LeanResearch.RepulsiveCoulomb.FiniteLinkComplementRefinement
public import LeanResearch.RepulsiveCoulomb.PointConstructedIncidentAngles

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The dependent finite index of coarse cells and
local subdivisions already carries the required order. Construct refined
target nodes by coarse cumulative starts and physical complement offsets;
two-stage interval coverage proves the whole disk cover without flattening
or making a new radial cut inside any occupied cell. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem exists_fin_consecutive_interval_cover {n : ℕ} (hn : 0 < n)
    (v : Fin (n + 1) → ℝ) {θ : ℝ} (hθ : θ ∈ Icc (v 0) (v (Fin.last n))) :
    ∃ i : Fin n, θ ∈ Icc (v i.castSucc) (v i.succ) := by
  let w : ℕ → ℝ := fun j ↦ if hj : j < n + 1 then v ⟨j, hj⟩ else 0
  have hfirst : w 0 = v 0 := by simp [w]
  have hlast : w n = v (Fin.last n) := by
    simp only [w, dif_pos (show n < n + 1 by omega)]
    exact congrArg v (Fin.ext rfl)
  obtain ⟨i, hi, hmem⟩ := exists_consecutive_interval_cover w n hn θ (by
    simpa only [hfirst, hlast] using hθ)
  refine ⟨⟨i, hi⟩, ?_⟩
  have hleft : w i = v (⟨i, hi⟩ : Fin n).castSucc := by
    simp only [w, dif_pos (show i < n + 1 by omega)]
    exact congrArg v (Fin.ext rfl)
  have hright : w (i + 1) = v (⟨i, hi⟩ : Fin n).succ := by
    simp only [w, dif_pos (show i + 1 < n + 1 by omega)]
    exact congrArg v (Fin.ext rfl)
  rw [hleft, hright] at hmem
  exact hmem

def refinedIncidentTargetNode
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (j : Fin N) (i : Fin (Q.count j + 1)) : ℝ := by
  classical
  exact linkCumulativeWidth (finiteLinkWidthSequence width) j.1 +
    if j ∈ range owner then (i.1 : ℝ) * width j
    else k * (Q.node j i - u j.castSucc)

theorem refinedIncidentTargetNode_first
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ) (j : Fin N) :
    refinedIncidentTargetNode Q width j 0 = linkCumulativeWidth (finiteLinkWidthSequence width) j.1 := by
  classical
  by_cases hj : j ∈ range owner <;> simp [refinedIncidentTargetNode, hj, Q.first]

theorem refinedIncidentTargetNode_last
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc)) (j : Fin N) :
    refinedIncidentTargetNode Q width j (Fin.last (Q.count j)) =
      linkCumulativeWidth (finiteLinkWidthSequence width) (j.1 + 1) := by
  classical
  rw [linkCumulativeWidth_succ]
  have hseq : finiteLinkWidthSequence width j.1 = width j := by simp [finiteLinkWidthSequence, j.2]
  rw [hseq]
  by_cases hj : j ∈ range owner
  · simp [refinedIncidentTargetNode, hj, Q.occupied_whole j hj]
  · simp only [refinedIncidentTargetNode, if_neg hj, Q.last]
    rw [← hcomp j hj]

theorem refinedIncidentTargetNode_step
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (j : Fin N) (i : Fin (Q.count j)) :
    refinedIncidentTargetNode Q width j i.succ - refinedIncidentTargetNode Q width j i.castSucc =
      refinedIncidentTargetWidth Q width j i := by
  classical
  by_cases hj : j ∈ range owner
  · simp only [refinedIncidentTargetNode, refinedIncidentTargetWidth, if_pos hj,
      Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [refinedIncidentTargetNode, refinedIncidentTargetWidth, if_neg hj]
    ring

theorem refinedIncidentTargetNode_strictMono
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (hk : 0 < k) (width : Fin N → ℝ)
    (hw : ∀ j, 0 < width j) (j : Fin N) :
    StrictMono (refinedIncidentTargetNode Q width j) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hpos := refinedIncidentTargetWidth_pos Q hk width hw j i
  rw [← refinedIncidentTargetNode_step] at hpos
  exact sub_pos.mp hpos

/-- The source subdivision covers each entire old cell, preserving all seam
endpoints. Applying a cone chart inverse therefore loses no complement point. -/
theorem finiteLinkComplementRefinement_source_cover
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (j : Fin N) {θ : ℝ}
    (hθ : θ ∈ Icc (u j.castSucc) (u j.succ)) :
    ∃ i : Fin (Q.count j), θ ∈ Icc (Q.node j i.castSucc) (Q.node j i.succ) := by
  apply exists_fin_consecutive_interval_cover (Q.count_pos j) (Q.node j)
  simpa only [Q.first, Q.last] using hθ

/-- Literal refined target disk cover indexed by a finite sigma type. The
2*pi sum is the previously proved scalar output; no flattening, target cover
certificate, or cyclic-order certificate is needed. -/
theorem refinedIncidentTargetWedges_cover
    {ι : Type*} {N : ℕ} (hN : 0 < N) {u : Fin (N + 1) → ℝ}
    {owner : ι ↪ Fin N} {k : ℝ} (Q : FiniteLinkComplementRefinement u owner k)
    (width : Fin N → ℝ)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc))
    (htotal : (∑ j, width j) = 2 * Real.pi) (R : ℝ) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∃ x : (Σ j : Fin N, Fin (Q.count j)),
      z ∈ flatLinkOccupiedDisk R
        (refinedIncidentTargetNode Q width x.1 x.2.castSucc)
        (refinedIncidentTargetNode Q width x.1 x.2.succ) := by
  have htotal' : linkCumulativeWidth (finiteLinkWidthSequence width) N = 2 * Real.pi := by
    rw [finiteLinkWidthSequence_total, htotal]
  obtain ⟨j, r, hr, θ, hθ, hzθ⟩ := orderedEuclideanWedges_cover hN
    (finiteLinkWidthSequence width) htotal' R hz
  have hθ' : θ ∈ Icc (refinedIncidentTargetNode Q width j 0)
      (refinedIncidentTargetNode Q width j (Fin.last (Q.count j))) := by
    simpa only [refinedIncidentTargetNode_first, refinedIncidentTargetNode_last Q width hcomp] using hθ
  obtain ⟨i, hi⟩ := exists_fin_consecutive_interval_cover (Q.count_pos j)
    (refinedIncidentTargetNode Q width j) hθ'
  exact ⟨⟨j, i⟩, r, hr, θ, hi, hzθ⟩


theorem refinedIncidentTargetWidth_le_pi
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (howned : ∀ j, j ∈ range owner → width j ≤ Real.pi)
    (j : Fin N) (i : Fin (Q.count j)) : refinedIncidentTargetWidth Q width j i ≤ Real.pi := by
  classical
  by_cases hj : j ∈ range owner
  · simpa only [refinedIncidentTargetWidth, if_pos hj] using howned j hj
  · simpa only [refinedIncidentTargetWidth, if_neg hj] using Q.complement_short j hj i

/-- The old full angular disk is covered as well; this is separate from and
prior to choosing physical branch maps into the new wedges. -/
theorem finiteLinkComplementRefinement_whole_source_cover
    {ι : Type*} {N : ℕ} (hN : 0 < N) {u : Fin (N + 1) → ℝ}
    (hu0 : u 0 = 0) (huT : u (Fin.last N) = 2 * Real.pi)
    {owner : ι ↪ Fin N} {k : ℝ} (Q : FiniteLinkComplementRefinement u owner k)
    (R : ℝ) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∃ x : (Σ j : Fin N, Fin (Q.count j)),
      z ∈ flatLinkOccupiedDisk R (Q.node x.1 x.2.castSucc) (Q.node x.1 x.2.succ) := by
  obtain ⟨θ, hθ, hzθ⟩ := exists_sectorPolar_nonnegative_angle z
  obtain ⟨j, hj⟩ := exists_fin_consecutive_interval_cover hN u (by
    simpa only [hu0, huT] using hθ)
  obtain ⟨i, hi⟩ := finiteLinkComplementRefinement_source_cover Q j hj
  exact ⟨⟨j, i⟩, ‖z‖, ⟨norm_nonneg _, hz⟩, θ, hi, hzθ⟩

end RepulsiveCoulomb
