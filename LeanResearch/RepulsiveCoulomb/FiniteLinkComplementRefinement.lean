import LeanResearch.RepulsiveCoulomb.PointIncidentCellAngleBalance
import LeanResearch.RepulsiveCoulomb.FiniteLinkPhysicalSubdivision
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! SOURCE-ONLY, UNCOMPILED. Keep occupied cells whole and physically
subdivide only complement cells. The refined widths remain positive and their
sum is proved equal to the previously derived actual target total. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

structure FiniteLinkComplementRefinement {ι : Type*} {N : ℕ}
    (u : Fin (N + 1) → ℝ) (owner : ι ↪ Fin N) (k : ℝ) where
  count : Fin N → ℕ
  count_pos : ∀ j, 0 < count j
  node : ∀ j, Fin (count j + 1) → ℝ
  strictMono : ∀ j, StrictMono (node j)
  first : ∀ j, node j 0 = u j.castSucc
  last : ∀ j, node j (Fin.last (count j)) = u j.succ
  occupied_whole : ∀ j, j ∈ range owner → count j = 1
  complement_short : ∀ j, j ∉ range owner → ∀ i : Fin (count j),
    k * (node j i.succ - node j i.castSucc) ≤ Real.pi

theorem exists_finiteLink_complement_refinement
    {ι : Type*} {N : ℕ} (u : Fin (N + 1) → ℝ) (hu : StrictMono u)
    (owner : ι ↪ Fin N) {k : ℝ} (hk : 0 < k) :
    Nonempty (FiniteLinkComplementRefinement u owner k) := by
  classical
  have build (j : Fin N) : ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → ℝ,
      StrictMono v ∧ v 0 = u j.castSucc ∧ v (Fin.last n) = u j.succ ∧
      (j ∈ range owner → n = 1) ∧
      (j ∉ range owner → ∀ i : Fin n, k * (v i.succ - v i.castSucc) ≤ Real.pi) := by
    have hj : u j.castSucc < u j.succ := hu (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    by_cases howned : j ∈ range owner
    · let v : Fin 2 → ℝ := fun i ↦ u j.castSucc + (i.1 : ℝ) * (u j.succ - u j.castSucc)
      refine ⟨1, by omega, v, ?_, ?_, ?_, (fun _ ↦ rfl), (fun h ↦ False.elim (h howned))⟩
      · intro i l hil
        simpa only [v, add_comm] using
          add_lt_add_left (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hil)
            (sub_pos.mpr hj)) (u j.castSucc)
      · simp [v]
      · dsimp [v]
        ring
    · obtain ⟨n, hn, v, hv, hv0, hvN, hsmall⟩ := exists_finite_physicalAngle_subdivision hj hk
      exact ⟨n, hn, v, hv, hv0, hvN, (fun h ↦ False.elim (howned h)), fun _ i ↦ (hsmall i).2⟩
  choose n hn v hv hv0 hvN hwhole hshort using build
  exact ⟨⟨n, hn, v, hv, hv0, hvN, hwhole, hshort⟩⟩

def refinedIncidentTargetWidth
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (j : Fin N) (i : Fin (Q.count j)) : ℝ := by
  classical
  exact if j ∈ range owner then width j else k * (Q.node j i.succ - Q.node j i.castSucc)

theorem refinedIncidentTargetWidth_pos
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (hk : 0 < k) (width : Fin N → ℝ)
    (hw : ∀ j, 0 < width j) (j : Fin N) (i : Fin (Q.count j)) :
    0 < refinedIncidentTargetWidth Q width j i := by
  classical
  unfold refinedIncidentTargetWidth
  split_ifs
  · exact hw j
  · exact mul_pos hk (sub_pos.mpr (Q.strictMono j (show i.castSucc < i.succ from Fin.castSucc_lt_succ)))

theorem refinedIncidentTargetWidth_cell_sum
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc)) (j : Fin N) :
    (∑ i, refinedIncidentTargetWidth Q width j i) = width j := by
  classical
  by_cases hj : j ∈ range owner
  · simp [refinedIncidentTargetWidth, hj, Q.occupied_whole j hj]
  · simp only [refinedIncidentTargetWidth, if_neg hj, ← Finset.mul_sum]
    rw [finiteLink_cell_width_sum, Q.first, Q.last, ← hcomp j hj]

theorem refinedIncidentTargetWidth_total
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    (Q : FiniteLinkComplementRefinement u owner k) (width : Fin N → ℝ)
    (hcomp : ∀ j, j ∉ range owner → width j = k * (u j.succ - u j.castSucc)) :
    (∑ x : (Σ j : Fin N, Fin (Q.count j)), refinedIncidentTargetWidth Q width x.1 x.2) =
      ∑ j, width j := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun j _ ↦ refinedIncidentTargetWidth_cell_sum Q width hcomp j)

end RepulsiveCoulomb
