import LeanResearch.RepulsiveCoulomb.FiniteLinkComplementTargetCover

/-! SOURCE-ONLY, UNCOMPILED. Two strict finite partitions with the same
coarse-cell and subcell indices have precisely the same node identifications.
Only boundary nodes are compared; no interior chart is replaced by an angular
interpolant. In particular this applies unchanged to nonradial passing pieces. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- An ordered two-level node system, allowing the two copies of each coarse
seam. The structure contains no assumed cross-system compatibility. -/
structure FiniteRefinedNodeSystem {N : ℕ} (count : Fin N → ℕ) where
  coarse : Fin (N + 1) → ℝ
  coarse_strict : StrictMono coarse
  node : ∀ j, Fin (count j + 1) → ℝ
  node_strict : ∀ j, StrictMono (node j)
  first : ∀ j, node j 0 = coarse j.castSucc
  last : ∀ j, node j (Fin.last (count j)) = coarse j.succ

namespace FiniteRefinedNodeSystem
variable {N : ℕ} {count : Fin N → ℕ}

theorem node_mem_cell (P : FiniteRefinedNodeSystem count)
    (j : Fin N) (i : Fin (count j + 1)) :
    P.node j i ∈ Icc (P.coarse j.castSucc) (P.coarse j.succ) := by
  constructor
  · rw [← P.first]
    exact (P.node_strict j).monotone (Fin.zero_le i)
  · rw [← P.last]
    exact (P.node_strict j).monotone (Fin.le_last i)

theorem node_mem_global (P : FiniteRefinedNodeSystem count)
    (j : Fin N) (i : Fin (count j + 1)) :
    P.node j i ∈ Icc (P.coarse 0) (P.coarse (Fin.last N)) :=
  ⟨(P.coarse_strict.monotone (Fin.zero_le j.castSucc)).trans (P.node_mem_cell j i).1,
    (P.node_mem_cell j i).2.trans (P.coarse_strict.monotone (Fin.le_last j.succ))⟩

/-- Equal nodes in distinct ordered coarse cells must be the two copies of
one adjacent coarse seam. The conclusion is derived from inequalities. -/
theorem node_eq_identifies_adjacent_seam (P : FiniteRefinedNodeSystem count)
    {j l : Fin N} (hjl : j < l)
    {i : Fin (count j + 1)} {t : Fin (count l + 1)}
    (he : P.node j i = P.node l t) :
    i = Fin.last (count j) ∧ t = 0 ∧ j.succ = l.castSucc := by
  have hbetween : P.coarse j.succ ≤ P.coarse l.castSucc :=
    P.coarse_strict.monotone (by change j.1 + 1 ≤ l.1; exact hjl)
  obtain ⟨hjiL, hjiR⟩ := P.node_mem_cell j i
  obtain ⟨hltL, hltR⟩ := P.node_mem_cell l t
  have hright : P.node j i = P.coarse j.succ := by linarith
  have hleft : P.node l t = P.coarse l.castSucc := by linarith
  have hcoarse : P.coarse j.succ = P.coarse l.castSucc := by linarith
  refine ⟨(P.node_strict j).injective ?_, (P.node_strict l).injective ?_,
    P.coarse_strict.injective hcoarse⟩
  · rw [P.last]
    exact hright
  · rw [P.first]
    exact hleft

/-- Scalar equality of nodes is transported between any such two systems. -/
theorem node_eq_transfer (P Q : FiniteRefinedNodeSystem count)
    {j l : Fin N} {i : Fin (count j + 1)} {t : Fin (count l + 1)}
    (he : P.node j i = P.node l t) : Q.node j i = Q.node l t := by
  rcases lt_trichotomy j l with hjl | hjl | hlj
  · obtain ⟨hi, ht, hseam⟩ := P.node_eq_identifies_adjacent_seam hjl he
    rw [hi, ht, Q.last, Q.first, hseam]
  · subst l
    exact congrArg (Q.node j) ((P.node_strict j).injective he)
  · obtain ⟨ht, hi, hseam⟩ := P.node_eq_identifies_adjacent_seam hlj he.symm
    rw [hi, ht, Q.first, Q.last, hseam]

theorem node_eq_iff (P Q : FiniteRefinedNodeSystem count)
    (j l : Fin N) (i : Fin (count j + 1)) (t : Fin (count l + 1)) :
    P.node j i = P.node l t ↔ Q.node j i = Q.node l t :=
  ⟨P.node_eq_transfer Q, Q.node_eq_transfer P⟩

/-- Being the global first node is likewise intrinsic to the node indices. -/
theorem node_eq_first_transfer (P Q : FiniteRefinedNodeSystem count)
    {j : Fin N} {i : Fin (count j + 1)} (he : P.node j i = P.coarse 0) :
    Q.node j i = Q.coarse 0 := by
  obtain ⟨hcellL, hcellR⟩ := P.node_mem_cell j i
  have hstart := P.coarse_strict.monotone (Fin.zero_le j.castSucc)
  have hcoarse : P.coarse j.castSucc = P.coarse 0 := by linarith
  have hj : j.castSucc = 0 := P.coarse_strict.injective hcoarse
  have hi : i = 0 := (P.node_strict j).injective (by rw [P.first]; linarith)
  rw [hi, Q.first, hj]

/-- Being the global last node is intrinsic as well, including the cut ray. -/
theorem node_eq_last_transfer (P Q : FiniteRefinedNodeSystem count)
    {j : Fin N} {i : Fin (count j + 1)}
    (he : P.node j i = P.coarse (Fin.last N)) :
    Q.node j i = Q.coarse (Fin.last N) := by
  obtain ⟨hcellL, hcellR⟩ := P.node_mem_cell j i
  have hend := P.coarse_strict.monotone (Fin.le_last j.succ)
  have hcoarse : P.coarse j.succ = P.coarse (Fin.last N) := by linarith
  have hj : j.succ = Fin.last N := P.coarse_strict.injective hcoarse
  have hi : i = Fin.last (count j) := (P.node_strict j).injective (by rw [P.last]; linarith)
  rw [hi, Q.last, hj]

end FiniteRefinedNodeSystem
end RepulsiveCoulomb
