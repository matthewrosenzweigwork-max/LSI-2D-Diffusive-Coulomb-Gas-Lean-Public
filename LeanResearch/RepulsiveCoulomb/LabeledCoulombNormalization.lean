module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-! Finite-positive normalization of the literal labeled Gibbs density.
The bound is deliberately allowed to depend on N; no uniform LSI is asserted. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem integrable_coulomb_gaussian (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : CoulombConfig N => Real.exp (-c * ‖z‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := CoulombConfig N)
    (b := (c : ℂ)) (by simpa using hc) 0 (0 : CoulombConfig N)
  convert! h.re using 1
  ext z
  simp only [zero_mul, add_zero]
  change Real.exp (-c * ‖z‖ ^ 2) = (Complex.exp (-(c : ℂ) * (‖z‖ : ℂ) ^ 2)).re
  rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.exp_ofReal_re]

def coulombRadialExponent (N : ℕ) (β : ℝ) : ℝ :=
  ∑ _p ∈ coulombPairs N, 2 * (β / (N : ℝ))

theorem coulomb_pair_rpow_le_exp {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (z : CoulombConfig N) (i j : Fin N) :
    ‖z i - z j‖ ^ (β / (N : ℝ)) ≤ Real.exp (2 * ‖z‖ * (β / (N : ℝ))) := by
  have hn : ‖z i - z j‖ ≤ 1 + 2 * ‖z‖ := by
    have ht := norm_sub_le (z i) (z j)
    have hi := PiLp.norm_apply_le z i
    have hj := PiLp.norm_apply_le z j
    linarith
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (div_nonneg hβ (Nat.cast_nonneg N))).trans
    (one_add_rpow_le_exp_mul (by positivity) (div_nonneg hβ (Nat.cast_nonneg N)))

theorem coulombWeight_le_gaussian {N : ℕ} {β : ℝ} (hβ : 0 < β) (z : CoulombConfig N) :
    coulombWeight β z ≤ Real.exp ((coulombRadialExponent N β) ^ 2 / β) *
      Real.exp (-(β / 4) * ‖z‖ ^ 2) := by
  have hp : (∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ ^ (β / (N : ℝ))) ≤
      Real.exp (‖z‖ * coulombRadialExponent N β) := by
    calc
      _ ≤ ∏ _p ∈ coulombPairs N, Real.exp (2 * ‖z‖ * (β / (N : ℝ))) :=
        Finset.prod_le_prod₀ (fun p _ => Real.rpow_nonneg (norm_nonneg _) _)
          (fun p _ => coulomb_pair_rpow_le_exp hβ.le z p.1 p.2)
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        simp only [coulombRadialExponent, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have h := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-β * ‖z‖ ^ 2 / 2)).le
  rw [← Real.exp_add] at h
  exact h.trans (gaussian_linear_le β (coulombRadialExponent N β) ‖z‖ hβ)

theorem coulombWeight_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Integrable (coulombWeight (N := N) β) := by
  refine ((integrable_coulomb_gaussian N (by positivity : 0 < β / 4)).const_mul
    (Real.exp ((coulombRadialExponent N β) ^ 2 / β))).mono'
      (coulombWeight_continuous hβ.le).aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (coulombWeight_nonneg β z)]
  exact coulombWeight_le_gaussian hβ z

theorem coulombPartition_lt_top {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    coulombPartition N β < ⊤ :=
  (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (coulombWeight_nonneg β))).mp
    (coulombWeight_integrable (N := N) hβ).hasFiniteIntegral

theorem coulombDomain_nonempty (N : ℕ) : (coulombDomain N : Set (CoulombConfig N)).Nonempty := by
  let z : CoulombConfig N := WithLp.toLp 2 (fun i : Fin N => (i.val : ℂ))
  refine ⟨z, (coulombVandermonde_ne_zero_iff z).mpr ?_⟩
  intro i j hij hz
  apply hij
  apply Fin.ext
  change (i.val : ℂ) = (j.val : ℂ) at hz
  exact_mod_cast hz

theorem coulombPartition_pos {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    0 < coulombPartition N β := by
  obtain ⟨z, hz⟩ := coulombDomain_nonempty N
  have hi := coulombWeight_integrable (N := N) hβ
  have hp : 0 < ∫ w : CoulombConfig N, coulombWeight β w :=
    integral_pos_of_integrable_nonneg_nonzero (coulombWeight_continuous hβ.le) hi
      (coulombWeight_nonneg β) (coulombWeight_pos_off_collisions β z hz).ne'
  rw [coulombPartition, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (coulombWeight_nonneg β))]
  exact ENNReal.ofReal_pos.mpr hp

theorem coulombMeasure_isProbability {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (coulombMeasure N β) := by
  constructor
  simp only [coulombMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (coulombPartition_pos (N := N) hβ).ne'
    (coulombPartition_lt_top (N := N) hβ).ne

end RepulsiveCoulomb
