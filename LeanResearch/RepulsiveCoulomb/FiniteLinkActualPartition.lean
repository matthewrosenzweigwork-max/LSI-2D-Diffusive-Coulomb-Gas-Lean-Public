import LeanResearch.RepulsiveCoulomb.FiniteLinkEndpointSubdivision
import Mathlib.Order.Fin.Basic

/-! SOURCE-ONLY, UNCOMPILED. Turn the explicitly sorted seam endpoints into
an indexed partition with its actual first and last coordinates. Any whole
occupied interval without another endpoint in its interior is proved to be
one whole partition cell; it is not subdivided by an assumed cell ownership. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_finiteLink_actual_partition {ι : Type*} [Fintype ι]
    {T : ℝ} (hT : 0 < T) (lo hi : ι → ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Fin (N + 1) → ℝ,
      StrictMono u ∧ u 0 = 0 ∧ u (Fin.last N) = T ∧
        range u = ↑(finiteLinkEndpointSet hT lo hi) := by
  classical
  let S := finiteLinkEndpointSet hT lo hi
  have h0S : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hTS : T ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcardpos : 0 < S.card := Finset.card_pos.mpr ⟨0, h0S⟩
  let N := S.card - 1
  have hcard : S.card = N + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ S.card)).symm
  let u : Fin (N + 1) ↪o ℝ := S.orderEmbOfFin hcard
  have hrange : range u = ↑S := Finset.range_orderEmbOfFin S hcard
  have hmem (i : Fin (N + 1)) : u i ∈ S := S.orderEmbOfFin_mem hcard i
  have hzero : u 0 = 0 := by
    have hzrange : (0 : ℝ) ∈ range u := by rw [hrange]; exact h0S
    obtain ⟨j, hj⟩ := hzrange
    apply le_antisymm
    · exact (u.monotone (Fin.zero_le j)).trans_eq hj
    · exact (finiteLinkEndpointSet_bounds hT lo hi (hmem 0)).1
  have hlast : u (Fin.last N) = T := by
    have hTrange : T ∈ range u := by rw [hrange]; exact hTS
    obtain ⟨j, hj⟩ := hTrange
    apply le_antisymm
    · exact (finiteLinkEndpointSet_bounds hT lo hi (hmem (Fin.last N))).2
    · exact hj.symm.trans_le (u.monotone (Fin.le_last j))
  have hN : 0 < N := by
    by_contra hn
    have hn0 : N = 0 := Nat.eq_zero_of_not_pos hn
    have hi : (0 : Fin (N + 1)) = Fin.last N := Fin.ext (by simp [hn0])
    have hbad : (0 : ℝ) = T := hzero.symm.trans ((congrArg u hi).trans hlast)
    exact hT.ne' hbad.symm
  exact ⟨N, hN, u, u.strictMono, hzero, hlast, hrange⟩

/-- An occupied arc with no hidden interior endpoints is one exact adjacent
cell of the actual partition. In particular a passing halfdisk stays whole. -/
theorem finiteLink_interval_is_whole_cell
    {N : ℕ} {S : Finset ℝ} (u : Fin (N + 1) → ℝ) (hu : StrictMono u)
    (hrange : range u = ↑S) {lo hi : ℝ} (hlo : lo ∈ S) (hhi : hi ∈ S)
    (hwidth : lo < hi) (hclear : ∀ x ∈ S, ¬ (lo < x ∧ x < hi)) :
    ∃ i : Fin N, u i.castSucc = lo ∧ u i.succ = hi := by
  have hlo' : lo ∈ range u := by rw [hrange]; exact hlo
  have hhi' : hi ∈ range u := by rw [hrange]; exact hhi
  obtain ⟨i, hi⟩ := hlo'
  obtain ⟨j, hj⟩ := hhi'
  have hij : i < j := (hu.lt_iff_lt).mp (by rwa [hi, hj])
  have hij' : i.1 < j.1 := hij
  have hjbound : j.1 < N + 1 := j.2
  have hin : i.1 < N := by omega
  have hnext : j.1 = i.1 + 1 := by
    by_contra hn
    have hgap : i.1 + 1 < j.1 := by omega
    let k : Fin (N + 1) := ⟨i.1 + 1, by omega⟩
    have hkmem : u k ∈ S := by
      change u k ∈ (↑S : Set ℝ)
      rw [← hrange]
      exact mem_range_self k
    apply hclear (u k) hkmem
    constructor
    · rw [← hi]
      exact hu (show i < k from Nat.lt_succ_self _)
    · rw [← hj]
      exact hu (show k < j from hgap)
  let k : Fin N := ⟨i.1, hin⟩
  have hleft : k.castSucc = i := Fin.ext rfl
  have hright : k.succ = j := Fin.ext hnext.symm
  refine ⟨k, ?_, ?_⟩
  · rw [hleft]
    exact hi
  · rw [hright]
    exact hj

end RepulsiveCoulomb
