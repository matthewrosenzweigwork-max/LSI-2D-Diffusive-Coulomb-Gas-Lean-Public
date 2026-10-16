module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombNormalization
public import LeanResearch.RepulsiveCoulomb.CoulombProductVolume

@[expose] public section

/-! Exact first-coordinate factorization with the unchanged pair exponent.
This is a density identity; normalized disintegration is a separate step. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombInteraction {N : ℕ} (α : ℝ) (z : CoulombConfig N) : ℝ :=
  ∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ ^ α

def coulombWeightAtExponent {N : ℕ} (γ α : ℝ) (z : CoulombConfig N) : ℝ :=
  Real.exp (-γ * ‖z‖ ^ 2 / 2) * coulombInteraction α z

theorem coulombWeight_eq_atExponent {N : ℕ} (β : ℝ) (z : CoulombConfig N) :
    coulombWeight β z = coulombWeightAtExponent β (β / (N : ℝ)) z := rfl

def coulombInsertZero {N : ℕ} (w : ℂ) (y : CoulombConfig N) : CoulombConfig (N + 1) :=
  WithLp.toLp 2 (Fin.cons w (fun j => y j))

theorem coulombInsertZero_zero {N : ℕ} (w : ℂ) (y : CoulombConfig N) :
    coulombInsertZero w y 0 = w := rfl

theorem coulombInsertZero_succ {N : ℕ} (w : ℂ) (y : CoulombConfig N) (j : Fin N) :
    coulombInsertZero w y j.succ = y j := rfl

theorem coulombInsertZero_norm_sq {N : ℕ} (w : ℂ) (y : CoulombConfig N) :
    ‖coulombInsertZero w y‖ ^ 2 = ‖w‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]
  rfl

theorem coulomb_pairs_prod_double {N : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin N → Fin N → M) :
    (∏ p ∈ coulombPairs N, f p.1 p.2) = ∏ i, ∏ j, if i < j then f i j else 1 := by
  rw [coulombPairs, Finset.prod_filter, Fintype.prod_prod_type]

theorem coulombInteraction_insert_zero {N : ℕ} (α : ℝ) (w : ℂ) (y : CoulombConfig N) :
    coulombInteraction α (coulombInsertZero w y) =
      (∏ j, ‖w - y j‖ ^ α) * coulombInteraction α y := by
  unfold coulombInteraction
  rw [coulomb_pairs_prod_double (fun i j : Fin (N + 1) => ‖coulombInsertZero w y i - coulombInsertZero w y j‖ ^ α),
    coulomb_pairs_prod_double (fun i j : Fin N => ‖y i - y j‖ ^ α)]
  rw [Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, Fin.not_lt_zero, Fin.succ_pos, Fin.succ_lt_succ_iff,
    if_false, if_true, one_mul, mul_one, coulombInsertZero_zero, coulombInsertZero_succ]

theorem coulombWeightAtExponent_insert_zero {N : ℕ} (γ α : ℝ) (w : ℂ) (y : CoulombConfig N) :
    coulombWeightAtExponent γ α (coulombInsertZero w y) =
      coulombWeightAtExponent γ α y * pointWeight γ (fun _ : Fin N => α) (fun j => y j) w := by
  rw [coulombWeightAtExponent, coulombInsertZero_norm_sq, coulombInteraction_insert_zero]
  have he : Real.exp (-γ * (‖w‖ ^ 2 + ‖y‖ ^ 2) / 2) =
      Real.exp (-γ * ‖w‖ ^ 2 / 2) * Real.exp (-γ * ‖y‖ ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold coulombWeightAtExponent pointWeight
  ring

theorem coulombWeight_one_site_factorization {N : ℕ} (β : ℝ) (w : ℂ) (y : CoulombConfig N) :
    coulombWeight β (coulombInsertZero w y) =
      coulombWeightAtExponent β (β / ((N + 1 : ℕ) : ℝ)) y *
        pointWeight β (fun _ : Fin N => β / ((N + 1 : ℕ) : ℝ)) (fun j => y j) w := by
  rw [coulombWeight_eq_atExponent, coulombWeightAtExponent_insert_zero]

theorem coulomb_one_site_exponent_sum_lt (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∑ _j : Fin N, β / ((N + 1 : ℕ) : ℝ)) < β := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mpr
  nlinarith

end RepulsiveCoulomb
