import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! The literal cyclic re-enumeration starting at any selected original
vertex. All finite bijection, adjacency, closing and predecessor facts are
proved for the concrete modular order. No cyclic-order certificate is assumed. -/
namespace RepulsiveCoulomb

def pointFiniteCyclicCornerOrder (n k i : ℕ) : ℕ := (k + i) % (n + 1)

theorem pointFiniteCyclicCornerOrder_le (n k i : ℕ) :
    pointFiniteCyclicCornerOrder n k i ≤ n := by
  have h := Nat.mod_lt (k + i) (Nat.zero_lt_succ n)
  exact Nat.lt_succ_iff.mp h

theorem pointFiniteCyclicCornerOrder_injective (n k : ℕ)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (heq : pointFiniteCyclicCornerOrder n k i = pointFiniteCyclicCornerOrder n k j) : i = j := by
  have hmod : Nat.ModEq (n + 1) (k + i) (k + j) := heq
  exact (hmod.add_left_cancel' k).eq_of_lt_of_lt (Nat.lt_succ_iff.mpr hi) (Nat.lt_succ_iff.mpr hj)

theorem pointFiniteCyclicCornerOrder_surjective (n k : ℕ) (hk : k ≤ n)
    {j : ℕ} (hj : j ≤ n) : ∃ i ≤ n, pointFiniteCyclicCornerOrder n k i = j := by
  by_cases hkj : k ≤ j
  · refine ⟨j - k, by omega, ?_⟩
    have heq : k + (j - k) = j := by omega
    simp only [pointFiniteCyclicCornerOrder, heq, Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hj)]
  · refine ⟨n + 1 + j - k, by omega, ?_⟩
    have heq : k + (n + 1 + j - k) = n + 1 + j := by omega
    simp only [pointFiniteCyclicCornerOrder, heq, Nat.add_mod, Nat.mod_self,
      zero_add, Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hj)]

@[simp] theorem pointFiniteCyclicCornerOrder_zero (n k : ℕ) (hk : k ≤ n) :
    pointFiniteCyclicCornerOrder n k 0 = k := by
  simp only [pointFiniteCyclicCornerOrder, Nat.add_zero, Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hk)]

theorem pointFiniteCyclicCornerOrder_succ (n k i : ℕ) :
    pointFiniteCyclicCornerOrder n k (i + 1) =
      if pointFiniteCyclicCornerOrder n k i = n then 0 else pointFiniteCyclicCornerOrder n k i + 1 := by
  have hmod : Nat.ModEq (n + 1) (k + i) (pointFiniteCyclicCornerOrder n k i) := by
    exact (Nat.mod_mod (k + i) (n + 1)).symm
  have hstep := hmod.add_right 1
  have heq : pointFiniteCyclicCornerOrder n k (i + 1) =
      (pointFiniteCyclicCornerOrder n k i + 1) % (n + 1) := by
    simpa only [Nat.ModEq, pointFiniteCyclicCornerOrder, Nat.add_assoc] using hstep
  rw [heq]
  by_cases hlast : pointFiniteCyclicCornerOrder n k i = n
  · rw [if_pos hlast, hlast, Nat.mod_self]
  · rw [if_neg hlast, Nat.mod_eq_of_lt]
    have hle := pointFiniteCyclicCornerOrder_le n k i
    omega

@[simp] theorem pointFiniteCyclicCornerOrder_wrap (n k : ℕ) (hk : k ≤ n) :
    pointFiniteCyclicCornerOrder n k (n + 1) = k := by
  simp only [pointFiniteCyclicCornerOrder, Nat.add_mod, Nat.mod_self, Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.lt_succ_iff.mpr hk)]

/-- Exact original endpoint matching survives the constructed rotation. -/
theorem pointFiniteCyclicCornerOrder_consecutive {T X : Type*} [Zero T] [One T]
    (f : ℕ → T → X) (n k : ℕ)
    (hv : ∀ j < n, f j 1 = f (j + 1) 0) (hclose : f n 1 = f 0 0) (i : ℕ) :
    f (pointFiniteCyclicCornerOrder n k i) 1 = f (pointFiniteCyclicCornerOrder n k (i + 1)) 0 := by
  rw [pointFiniteCyclicCornerOrder_succ]
  by_cases hlast : pointFiniteCyclicCornerOrder n k i = n
  · rw [if_pos hlast, hlast]
    exact hclose
  · rw [if_neg hlast]
    exact hv _ (lt_of_le_of_ne (pointFiniteCyclicCornerOrder_le n k i) hlast)

theorem pointFiniteCyclicCornerOrder_closing {T X : Type*} [Zero T] [One T]
    (f : ℕ → T → X) (n k : ℕ) (hk : k ≤ n)
    (hv : ∀ j < n, f j 1 = f (j + 1) 0) (hclose : f n 1 = f 0 0) :
    f (pointFiniteCyclicCornerOrder n k n) 1 = f (pointFiniteCyclicCornerOrder n k 0) 0 := by
  have h := pointFiniteCyclicCornerOrder_consecutive f n k hv hclose n
  simpa only [pointFiniteCyclicCornerOrder_wrap n k hk, pointFiniteCyclicCornerOrder_zero n k hk] using h

/-- The final incoming edge is the literal cyclic predecessor of the
selected outgoing edge, also in the two-edge case. -/
theorem pointFiniteCyclicCornerOrder_last (n k : ℕ) (hk : k ≤ n) :
    pointFiniteCyclicCornerOrder n k n = if k = 0 then n else k - 1 := by
  by_cases hk0 : k = 0
  · subst k
    simp [pointFiniteCyclicCornerOrder, Nat.mod_eq_of_lt (Nat.lt_succ_self n)]
  · rw [if_neg hk0]
    have heq : k + n = n + 1 + (k - 1) := by omega
    have hlt : k - 1 < n + 1 := by omega
    simp only [pointFiniteCyclicCornerOrder, heq, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_eq_of_lt hlt]

end RepulsiveCoulomb
