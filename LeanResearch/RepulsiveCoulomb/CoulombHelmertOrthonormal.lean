module

public import LeanResearch.RepulsiveCoulomb.CoulombHelmertCoefficients

@[expose] public section

/-! Exact all-particle Helmert orthonormal basis, with the order and signs
printed in proposition `prop:com` of the canonical manuscript. -/
noncomputable section
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The first Helmert coefficient is constant on every particle. -/
def coulombHelmertCenterScale (n : ℕ) : ℝ := (Real.sqrt (n + 1 : ℝ))⁻¹

theorem coulombHelmertCenterScale_sq (n : ℕ) :
    coulombHelmertCenterScale n * coulombHelmertCenterScale n * (n + 1 : ℝ) = 1 := by
  have hp : 0 < (n + 1 : ℝ) := by positivity
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hsq := Real.sq_sqrt hp.le
  unfold coulombHelmertCenterScale
  field_simp
  nlinarith

/-- Rows of the real Helmert matrix, embedded in the complex configuration. -/
def coulombHelmertRow (n : ℕ) : Fin (n + 1) → CoulombConfig (n + 1) :=
  Fin.cases (coulombHelmertRealVector (fun _ => coulombHelmertCenterScale n))
    (fun k => coulombHelmertRealVector
      (fun j => coulombHelmertScale (k.val + 1) * coulombHelmertRaw k.succ j))

theorem coulombHelmertRow_zero (n : ℕ) :
    coulombHelmertRow n 0 =
      coulombHelmertRealVector (fun _ => coulombHelmertCenterScale n) := rfl

theorem coulombHelmertRow_succ (n : ℕ) (k : Fin n) :
    coulombHelmertRow n k.succ =
      coulombHelmertRealVector
        (fun j => coulombHelmertScale (k.val + 1) * coulombHelmertRaw k.succ j) := rfl

private theorem coulombHelmert_sum_scaled_mul {N : ℕ} (a b : ℝ)
    (f g : Fin N → ℝ) :
    (∑ j, (a * f j) * (b * g j)) = a * b * ∑ j, f j * g j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem coulombHelmertRow_inner_zero_zero (n : ℕ) :
    inner ℂ (coulombHelmertRow n 0) (coulombHelmertRow n 0) = 1 := by
  rw [coulombHelmertRow_zero, coulombHelmertRealVector_inner]
  have h : (∑ _j : Fin (n + 1),
      coulombHelmertCenterScale n * coulombHelmertCenterScale n) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    convert coulombHelmertCenterScale_sq n using 1 <;> push_cast <;> ring
  rw [h]
  norm_num

theorem coulombHelmertRow_inner_zero_succ (n : ℕ) (k : Fin n) :
    inner ℂ (coulombHelmertRow n 0) (coulombHelmertRow n k.succ) = 0 := by
  rw [coulombHelmertRow_zero, coulombHelmertRow_succ,
    coulombHelmertRealVector_inner]
  simp only [← Finset.mul_sum, coulombHelmertRaw_sum, mul_zero, Complex.ofReal_zero]

theorem coulombHelmertRow_inner_succ_self (n : ℕ) (k : Fin n) :
    inner ℂ (coulombHelmertRow n k.succ) (coulombHelmertRow n k.succ) = 1 := by
  rw [coulombHelmertRow_succ, coulombHelmertRealVector_inner,
    coulombHelmert_sum_scaled_mul, coulombHelmertRaw_sum_square]
  have hs := coulombHelmertScale_sq (k.val + 1) (by omega)
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at hs ⊢
  rw [hs]
  norm_num

theorem coulombHelmertRow_inner_succ_ne (n : ℕ) {k l : Fin n} (hkl : k ≠ l) :
    inner ℂ (coulombHelmertRow n k.succ) (coulombHelmertRow n l.succ) = 0 := by
  have hsucc : k.succ ≠ l.succ := fun h => hkl (Fin.succ_injective n h)
  rw [coulombHelmertRow_succ, coulombHelmertRow_succ,
    coulombHelmertRealVector_inner, coulombHelmert_sum_scaled_mul,
    coulombHelmertRaw_sum_mul hsucc]
  simp

theorem coulombHelmertRow_orthonormal (n : ℕ) :
    Orthonormal ℂ (coulombHelmertRow n) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.cases ?_ (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa using coulombHelmertRow_inner_zero_zero n
    · simpa [Ne.symm (Fin.succ_ne_zero l)] using coulombHelmertRow_inner_zero_succ n l
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa using (inner_eq_zero_symm.1 (coulombHelmertRow_inner_zero_succ n k))
    · by_cases hkl : k = l
      · subst l
        simpa using coulombHelmertRow_inner_succ_self n k
      · simpa [hkl] using coulombHelmertRow_inner_succ_ne n hkl

/-- The manuscript's coefficient vectors, as an exact complex orthonormal basis. -/
def coulombHelmertBasis (n : ℕ) :
    OrthonormalBasis (Fin (n + 1)) ℂ (CoulombConfig (n + 1)) :=
  OrthonormalBasis.mk (coulombHelmertRow_orthonormal n)
    ((coulombHelmertRow_orthonormal n).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [CoulombConfig])).ge

theorem coulombHelmertBasis_apply (n : ℕ) (i : Fin (n + 1)) :
    coulombHelmertBasis n i = coulombHelmertRow n i := by
  simp [coulombHelmertBasis]

/-- Literal all-N Helmert coordinate transformation, complex unitary. -/
def coulombHelmertEquiv (n : ℕ) :
    CoulombConfig (n + 1) ≃ₗᵢ[ℂ] CoulombConfig (n + 1) :=
  (coulombHelmertBasis n).repr

theorem coulombHelmertEquiv_apply (n : ℕ) (z : CoulombConfig (n + 1))
    (i : Fin (n + 1)) :
    coulombHelmertEquiv n z i = inner ℂ (coulombHelmertRow n i) z := by
  rw [coulombHelmertEquiv, OrthonormalBasis.repr_apply_apply, coulombHelmertBasis_apply]

end RepulsiveCoulomb
