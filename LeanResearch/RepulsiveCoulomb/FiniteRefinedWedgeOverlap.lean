module

public import LeanResearch.RepulsiveCoulomb.FiniteRefinedCyclicSeam

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Distinct cells in a two-level strict angular
partition meet only along their endpoint rays, including the cyclic cut ray.
This is a conclusion of ordered nodes and one full period, not an atlas field. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
namespace FiniteRefinedNodeSystem
variable {N : ℕ} {count : Fin N → ℕ}

def cellLower (P : FiniteRefinedNodeSystem count)
    (x : Σ j : Fin N, Fin (count j)) : ℝ := P.node x.1 x.2.castSucc

def cellUpper (P : FiniteRefinedNodeSystem count)
    (x : Σ j : Fin N, Fin (count j)) : ℝ := P.node x.1 x.2.succ

def cellEndpoint (P : FiniteRefinedNodeSystem count)
    (x : Σ j : Fin N, Fin (count j)) (top : Bool) : ℝ :=
  if top then P.cellUpper x else P.cellLower x

/-- Distinct refined cells are linearly separated before identifying 0 and
2*pi. This comparison uses both levels of their actual finite sigma index. -/
theorem cells_separated (P : FiniteRefinedNodeSystem count)
    (x y : Σ j : Fin N, Fin (count j)) (hne : x ≠ y) :
    P.cellUpper x ≤ P.cellLower y ∨ P.cellUpper y ≤ P.cellLower x := by
  rcases x with ⟨j, i⟩
  rcases y with ⟨l, t⟩
  change P.node j i.succ ≤ P.node l t.castSucc ∨
    P.node l t.succ ≤ P.node j i.castSucc
  rcases lt_trichotomy j l with hjl | hjl | hlj
  · left
    exact (P.node_mem_cell j i.succ).2.trans
      ((P.coarse_strict.monotone (by change j.1 + 1 ≤ l.1; exact hjl)).trans
        (P.node_mem_cell l t.castSucc).1)
  · subst l
    rcases lt_trichotomy i t with hit | hit | hti
    · left
      exact (P.node_strict j).monotone (by change i.1 + 1 ≤ t.1; exact hit)
    · subst t
      exact False.elim (hne rfl)
    · right
      exact (P.node_strict j).monotone (by change t.1 + 1 ≤ i.1; exact hti)
  · right
    exact (P.node_mem_cell l t.succ).2.trans
      ((P.coarse_strict.monotone (by change l.1 + 1 ≤ j.1; exact hlj)).trans
        (P.node_mem_cell j i.castSucc).1)

theorem cell_mem_global (P : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (x : Σ j : Fin N, Fin (count j)) {θ : ℝ}
    (hθ : θ ∈ Icc (P.cellLower x) (P.cellUpper x)) :
    θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
  have hlo := P.node_mem_global x.1 x.2.castSucc
  have hhi := P.node_mem_global x.1 x.2.succ
  rw [hP0, hPT] at hlo hhi
  exact ⟨hlo.1.trans hθ.1, hθ.2.trans hhi.2⟩

/-- A scalar angle in two distinct closed cells must be an endpoint of each. -/
theorem common_angle_is_endpoint (P : FiniteRefinedNodeSystem count)
    (x y : Σ j : Fin N, Fin (count j)) (hne : x ≠ y) {θ : ℝ}
    (hx : θ ∈ Icc (P.cellLower x) (P.cellUpper x))
    (hy : θ ∈ Icc (P.cellLower y) (P.cellUpper y)) :
    (θ = P.cellLower x ∨ θ = P.cellUpper x) ∧
      (θ = P.cellLower y ∨ θ = P.cellUpper y) := by
  rcases P.cells_separated x y hne with hxy | hyx
  · exact ⟨Or.inr (by linarith [hx.2, hy.1]), Or.inl (by linarith [hx.2, hy.1])⟩
  · exact ⟨Or.inl (by linarith [hy.2, hx.1]), Or.inr (by linarith [hy.2, hx.1])⟩

theorem global_end_is_cell_endpoint (P : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (x : Σ j : Fin N, Fin (count j)) {θ : ℝ}
    (hθ : θ ∈ Icc (P.cellLower x) (P.cellUpper x))
    (hend : θ = 0 ∨ θ = 2 * Real.pi) :
    θ = P.cellLower x ∨ θ = P.cellUpper x := by
  have hlo := P.node_mem_global x.1 x.2.castSucc
  have hhi := P.node_mem_global x.1 x.2.succ
  rw [hP0, hPT] at hlo hhi
  change 0 ≤ P.cellLower x ∧ P.cellLower x ≤ 2 * Real.pi at hlo
  change 0 ≤ P.cellUpper x ∧ P.cellUpper x ≤ 2 * Real.pi at hhi
  rcases hend with h0 | hT
  · exact Or.inl (by linarith [hθ.1, hlo.1])
  · exact Or.inr (by linarith [hθ.2, hhi.2])

/-- Every noncentral intersection point of distinct wedges is on an endpoint
ray of each, with one common positive radial parameter. The proof includes
0/2*pi intersections and does not assume interval interiors are disjoint. -/
theorem nonzero_wedge_overlap_endpoints (P : FiniteRefinedNodeSystem count)
    (hP0 : P.coarse 0 = 0) (hPT : P.coarse (Fin.last N) = 2 * Real.pi)
    (x y : Σ j : Fin N, Fin (count j)) (hne : x ≠ y)
    {R S : ℝ} {z : ℂ} (hz0 : z ≠ 0)
    (hzx : z ∈ flatLinkOccupiedDisk R (P.cellLower x) (P.cellUpper x))
    (hzy : z ∈ flatLinkOccupiedDisk S (P.cellLower y) (P.cellUpper y)) :
    ∃ r : ℝ, 0 < r ∧ ∃ b c : Bool,
      z = sectorPolar r (P.cellEndpoint x b) ∧
      z = sectorPolar r (P.cellEndpoint y c) := by
  obtain ⟨r, hr, θ, hθ, hzθ⟩ := hzx
  obtain ⟨s, hs, φ, hφ, hzφ⟩ := hzy
  have hrs : r = s := by
    have hn := congrArg norm (hzθ.symm.trans hzφ)
    simpa only [sectorPolar_norm hr.1, sectorPolar_norm hs.1] using hn
  subst s
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr.1
    intro he
    apply hz0
    rw [hzθ, ← he, sectorPolar_zero]
  have hglobalθ := P.cell_mem_global hP0 hPT x hθ
  have hglobalφ := P.cell_mem_global hP0 hPT y hφ
  have hend : (θ = P.cellLower x ∨ θ = P.cellUpper x) ∧
      (φ = P.cellLower y ∨ φ = P.cellUpper y) := by
    rcases (sectorPolar_eq_iff_closed_period hrpos hglobalθ hglobalφ).mp
      (hzθ.symm.trans hzφ) with he | ⟨h0, hT⟩ | ⟨hT, h0⟩
    · subst φ
      exact P.common_angle_is_endpoint x y hne hθ hφ
    · exact ⟨P.global_end_is_cell_endpoint hP0 hPT x hθ (Or.inl h0),
        P.global_end_is_cell_endpoint hP0 hPT y hφ (Or.inr hT)⟩
    · exact ⟨P.global_end_is_cell_endpoint hP0 hPT x hθ (Or.inr hT),
        P.global_end_is_cell_endpoint hP0 hPT y hφ (Or.inl h0)⟩
  rcases hend with ⟨hx | hx, hy | hy⟩
  · exact ⟨r, hrpos, false, false, by simpa [cellEndpoint, hx] using hzθ,
      by simpa [cellEndpoint, hy] using hzφ⟩
  · exact ⟨r, hrpos, false, true, by simpa [cellEndpoint, hx] using hzθ,
      by simpa [cellEndpoint, hy] using hzφ⟩
  · exact ⟨r, hrpos, true, false, by simpa [cellEndpoint, hx] using hzθ,
      by simpa [cellEndpoint, hy] using hzφ⟩
  · exact ⟨r, hrpos, true, true, by simpa [cellEndpoint, hx] using hzθ,
      by simpa [cellEndpoint, hy] using hzφ⟩

end FiniteRefinedNodeSystem
end RepulsiveCoulomb
