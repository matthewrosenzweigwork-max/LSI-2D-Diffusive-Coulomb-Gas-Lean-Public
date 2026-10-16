module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

/-! Finite-dimensional spectral conversion of a genuine Bochner inequality. -/
noncomputable section
open scoped BigOperators
open InnerProductSpace
namespace RepulsiveCoulomb

theorem finiteDimensional_gap_of_bochner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] E) (hL : L.IsPositive) {c : ℝ} (hc : 0 < c)
    (hB : ∀ x : E, c * inner ℝ x (L x) ≤ ‖L x‖ ^ 2)
    (x : E) (hx : x ∈ L.kerᗮ) :
    c * ‖x‖ ^ 2 ≤ inner ℝ x (L x) := by
  let b := hL.isSymmetric.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let ev := hL.isSymmetric.eigenvalues (n := Module.finrank ℝ E) rfl
  have heig (i : Fin (Module.finrank ℝ E)) : L (b i) = ev i • b i :=
    hL.isSymmetric.apply_eigenvectorBasis rfl i
  have hev0 (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i := hL.nonneg_eigenvalues rfl i
  have hev (i : Fin (Module.finrank ℝ E)) : ev i = 0 ∨ c ≤ ev i := by
    have h := hB (b i)
    rw [heig i, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_smul, Real.norm_eq_abs, b.norm_eq_one, mul_one, one_pow, mul_one, sq_abs] at h
    by_cases hz : ev i = 0
    · exact Or.inl hz
    · have hp : 0 < ev i := lt_of_le_of_ne (hev0 i) (Ne.symm hz)
      exact Or.inr ((mul_le_mul_iff_left₀ hp).mp (by simpa only [pow_two] using h))
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      inner ℝ (b i) (L x) = ev i * inner ℝ (b i) x := by
    have h := hL.isSymmetric.eigenvectorBasis_apply_self_apply (n := Module.finrank ℝ E) rfl x i
    change b.repr (L x) i = ev i * b.repr x i at h
    simpa only [b.repr_apply_apply] using h
  have hform : inner ℝ x (L x) = ∑ i, ev i * (inner ℝ (b i) x) ^ 2 := by
    rw [← b.sum_inner_mul_inner x (L x)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i]
    simp only [real_inner_comm (b i) x]
    ring
  rw [hform, ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rcases hev i with hz | hp
  · have hk : b i ∈ L.ker := by
      rw [LinearMap.mem_ker, heig i, hz, zero_smul]
    have hzero := Submodule.inner_right_of_mem_orthogonal hk hx
    rw [hzero]
    simp
  · exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)

end RepulsiveCoulomb

