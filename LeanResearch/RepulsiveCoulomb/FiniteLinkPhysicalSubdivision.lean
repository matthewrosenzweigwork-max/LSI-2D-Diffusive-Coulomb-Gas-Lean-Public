module

public import LeanResearch.RepulsiveCoulomb.FiniteLinkEndpointSubdivision
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Construct a finite subdivision into physical
angles at most pi. This is necessary even for an unchanged complement gap:
its full-cone physical angle may be larger than pi. No complement gap is
discarded or silently represented by the shorter circular angle. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Equal subdivision in actual unwrapped angular coordinates. The positive
cone factor converts normalized chart angle to physical angle. -/
theorem exists_finite_physicalAngle_subdivision {l r k : ℝ}
    (hlr : l < r) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin (n + 1) → ℝ,
      StrictMono u ∧ u 0 = l ∧ u (Fin.last n) = r ∧
        ∀ i : Fin n, 0 < k * (u i.succ - u i.castSucc) ∧
          k * (u i.succ - u i.castSucc) ≤ Real.pi := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k * (r - l) / Real.pi)
  let n := N + 1
  have hn : 0 < n := Nat.succ_pos N
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hstep : 0 < (r - l) / (n : ℝ) := div_pos (sub_pos.mpr hlr) hnR
  have hsmall : k * ((r - l) / (n : ℝ)) ≤ Real.pi := by
    have hN' : k * (r - l) < (N : ℝ) * Real.pi :=
      (div_lt_iff₀ Real.pi_pos).mp hN
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hnR).mpr
    dsimp [n]
    push_cast
    nlinarith [Real.pi_pos]
  let u : Fin (n + 1) → ℝ := fun i ↦ l + (i.1 : ℝ) * ((r - l) / (n : ℝ))
  have hmono : StrictMono u := by
    intro i j hij
    have hcast : (i.1 : ℝ) < (j.1 : ℝ) := Nat.cast_lt.mpr hij
    simpa only [u, add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right hcast hstep) l
  have hzero : u 0 = l := by simp [u]
  have hlast : u (Fin.last n) = r := by
    dsimp [u]
    rw [mul_div_cancel₀ _ (ne_of_gt hnR)]
    ring
  refine ⟨n, hn, u, hmono, hzero, hlast, fun i ↦ ?_⟩
  have hdiff : u i.succ - u i.castSucc = (r - l) / (n : ℝ) := by
    dsimp [u]
    push_cast
    ring
  rw [hdiff]
  exact ⟨mul_pos hk hstep, hsmall⟩

/-- Apply the actual construction to every finite endpoint gap, including
unchanged gaps. There is no finite cyclic-order or short-piece premise here. -/
theorem exists_finiteLinkGap_physical_subdivision {S : Finset ℝ}
    (G : FiniteLinkGap S) {k : ℝ} (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin (n + 1) → ℝ,
      StrictMono u ∧ u 0 = G.left ∧ u (Fin.last n) = G.right ∧
        ∀ i : Fin n, 0 < k * (u i.succ - u i.castSucc) ∧
          k * (u i.succ - u i.castSucc) ≤ Real.pi :=
  exists_finite_physicalAngle_subdivision G.2.1 hk

end RepulsiveCoulomb
