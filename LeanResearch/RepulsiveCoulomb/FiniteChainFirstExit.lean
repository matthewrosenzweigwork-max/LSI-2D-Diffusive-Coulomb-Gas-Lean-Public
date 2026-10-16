module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A finite chain with step at most2 has a full-edge crossing prefix inside the
exact doubled ball when R>=16. This is an intermediate unit-mesh statement. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem finite_chain_first_exit (p : ℕ → ℂ) (n : ℕ) (c : ℂ) {R : ℝ}
    (hR : 16 ≤ R) (hstart : dist (p 0) c ≤ 5 * R / 4)
    (hfar : ∃ j ≤ n, 7 * R / 4 ≤ dist (p j) c)
    (hstep : ∀ j < n, dist (p j) (p (j + 1)) ≤ 2) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ R / 2 ≤ dist (p k) (p 0) ∧
      (∀ j ≤ k, p j ∈ ball c (2 * R)) ∧
      (∀ j < k, segment ℝ (p j) (p (j + 1)) ⊆ ball c (2 * R)) := by
  classical
  let k := Nat.find hfar
  have hk := Nat.find_spec hfar
  change k ≤ n ∧ 7 * R / 4 ≤ dist (p k) c at hk
  have hbefore : ∀ j < k, dist (p j) c < 7 * R / 4 := by
    intro j hj
    have hn := Nat.find_min hfar hj
    change ¬ (j ≤ n ∧ 7 * R / 4 ≤ dist (p j) c) at hn
    exact lt_of_not_ge (fun h => hn ⟨by omega,h⟩)
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    linarith [hk.2]
  obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hlast : dist (p k) c < 2 * R := by
    have hlk : l < k := by omega
    have hlB := hbefore l hlk
    have hls := hstep l (by omega)
    have htri := dist_triangle (p k) (p l) c
    have hrev : dist (p k) (p l) ≤ 2 := by simpa [hl,dist_comm] using hls
    linarith
  have hball : ∀ j ≤ k, p j ∈ ball c (2 * R) := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · have hh := hbefore j hj
      exact mem_ball.mpr (by linarith)
    · exact mem_ball.mpr hlast
  refine ⟨k,hkpos,hk.1,?_,hball,?_⟩
  · have htri := dist_triangle (p k) (p 0) c
    linarith [hk.2]
  · intro j hj
    exact (convex_ball c (2 * R)).segment_subset (hball j (by omega)) (hball (j+1) (by omega))

end RepulsiveCoulomb
