module

public import LeanResearch.RepulsiveCoulomb.PointFiniteRadialCornerGeometry
public import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryCoalescence

@[expose] public section

/-! A corner record's final incoming edge is determined by the original
family's endpoint matching and actual vertex injectivity. No knowledge of
how the record's cyclic order was constructed is needed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem PointFiniteRadialCornerAt.incoming_index_eq
    {f : ℕ → ℝ → ℂ} {n k : ℕ} {θ : ℝ} (D : PointFiniteRadialCornerAt f n k θ)
    (hv : ∀ i < n, f i 1 = f (i + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t) :
    D.order n = if k = 0 then n else k - 1 := by
  have hk : k ≤ n := by simpa only [D.order_zero] using D.order_le 0 (Nat.zero_le n)
  have hlastle : D.order n ≤ n := D.order_le n le_rfl
  have hend : f (D.order n) 1 = f k 0 := by simpa only [D.order_zero] using D.closing
  by_cases hlast : D.order n = n
  · have hend' : f n 1 = f k 0 := by simpa only [hlast] using hend
    have hzero : 0 = k := finite_halfOpen_simple_vertices_injective f n hinj
      0 (Nat.zero_le n) k hk (hclose.symm.trans hend')
    have hk0 : k = 0 := hzero.symm
    rw [if_pos hk0]
    exact hlast
  · have hlt : D.order n < n := lt_of_le_of_ne hlastle hlast
    have hnext : f (D.order n + 1) 0 = f k 0 := (hv _ hlt).symm.trans hend
    have hnextk : D.order n + 1 = k := finite_halfOpen_simple_vertices_injective f n hinj
      (D.order n + 1) (Nat.succ_le_iff.mpr hlt) k hk hnext
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0]
    omega

end RepulsiveCoulomb
