import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDerivativeBounds
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFirstDerivativeTail

/-! Quantitative tails of every physical Fréchet derivative of the actually
constructed thermal density. The induction derives global bounds for all
lower derivatives from their Gaussian tails, transfers them to radial
averaging, and uses the exact Cartesian score. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology RealInnerProductSpace
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The manuscript polynomial exponent is exactly beta+n. -/
def equilibriumDensityDerivativeWeight (β : ℝ) (n : ℕ) (x : ℂ) : ℝ :=
  equilibriumPolynomialGaussian (β + (n : ℝ)) (β / 2) x

theorem equilibriumDensityDerivativeWeight_nonneg (β : ℝ) (n : ℕ) (x : ℂ) :
    0 ≤ equilibriumDensityDerivativeWeight β n x :=
  equilibriumPolynomialGaussian_nonneg _ _ _

theorem equilibriumDensityDerivativeWeight_succ (β : ℝ) (n : ℕ) (x : ℂ) :
    equilibriumDensityDerivativeWeight β (n + 1) x =
      equilibriumDensityDerivativeWeight β n x * (1 + ‖x‖) := by
  unfold equilibriumDensityDerivativeWeight equilibriumPolynomialGaussian
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
    Real.rpow_add (by positivity : 0 < 1 + ‖x‖), Real.rpow_one]
  ring

theorem equilibriumDensityDerivativeWeight_le_succ (β : ℝ) (n : ℕ) (x : ℂ) :
    equilibriumDensityDerivativeWeight β n x ≤ equilibriumDensityDerivativeWeight β (n + 1) x := by
  rw [equilibriumDensityDerivativeWeight_succ]
  nlinarith [equilibriumDensityDerivativeWeight_nonneg β n x, norm_nonneg x]

/-- A common Gaussian tail through order n supplies a finite common global
bound, derived from the Gaussian rather than assumed. -/
theorem equilibriumDensityDerivativeWeight_global_bound {β : ℝ} (hβ : 0 < β)
    (n : ℕ) (x : ℂ) :
    equilibriumDensityDerivativeWeight β n x ≤
      Real.exp ((β + (n : ℝ)) ^ 2 / (2 * (β / 2))) := by
  have h := equilibriumPolynomialGaussian_bound
    (by positivity : 0 ≤ β + (n : ℝ)) (half_pos hβ) x
  have he : Real.exp (-(β / 2 / 2) * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

/-- One actual derivative step. The hypothesis is the induction information
through order n; every bound used for the coefficient J is derived from it. -/
theorem equilibriumReference_derivative_tail_step {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (n : ℕ) {C : ℝ} (hC : 0 < C)
    (hprior : ∀ j ≤ n, ∀ x : ℂ, ‖iteratedFDeriv ℝ j R.density x‖ ≤
      C * equilibriumDensityDerivativeWeight β n x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℂ, ‖iteratedFDeriv ℝ (n + 1) R.density x‖ ≤
      B * equilibriumDensityDerivativeWeight β (n + 1) x := by
  let D : ℝ := C * Real.exp ((β + (n : ℝ)) ^ 2 / (2 * (β / 2)))
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hglobal : ∀ j ≤ n, ∀ x : ℂ, ‖iteratedFDeriv ℝ j R.density x‖ ≤ D := by
    intro j hj x
    exact (hprior j hj x).trans
      (mul_le_mul_of_nonneg_left (equilibriumDensityDerivativeWeight_global_bound hβ n x) hC.le)
  have hJ : ∀ j ≤ n, ∀ x : ℂ,
      ‖iteratedFDeriv ℝ j (equilibriumRadialAverage R.density) x‖ ≤ D := by
    intro j hj x
    exact equilibriumRadialAverage_iteratedFDeriv_norm_le j R.smooth (fun _ => D)
      (fun _ _ => hD0) (fun i hi => hglobal i (hi.trans hj)) x
  let a : ℂ → ℝ := fun x => -β + (2 * β * Real.pi) * equilibriumRadialAverage R.density x
  let A : ℝ := β + (2 * β * Real.pi) * D
  let S : ℝ := equilibriumLeibnizConstant n
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hS : 0 ≤ S := (equilibriumLeibnizConstant_pos n).le
  have hJsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (equilibriumRadialAverage R.density) :=
    equilibriumRadialAverage_contDiff R.smooth
  have hasmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := contDiff_const.add (contDiff_const.mul hJsmooth)
  have habound : ∀ j ≤ n, ∀ x : ℂ, ‖iteratedFDeriv ℝ j a x‖ ≤ A := by
    intro j hj x
    have h := equilibrium_iteratedFDeriv_affine_norm_le hJsmooth (-β) (2 * β * Real.pi)
      j x (hJ j hj x)
    simpa only [abs_neg, abs_of_pos hβ, abs_of_nonneg (by positivity : 0 ≤ 2 * β * Real.pi)] using h
  have hfd : fderiv ℝ R.density = (fun x => (a x * R.density x) • innerSL ℝ x) := by
    funext x
    rw [(equilibrium_pointwise_EL_hasFDerivAt_score hβ R.smooth.continuous.measurable
      R.positive R.cap R.integrable R.mass_one R.secondMoment_integrable R.radial R.eulerLagrange x).fderiv]
    unfold equilibriumScoreDerivative
    congr 1
    dsimp only [a]
    ring
  let B : ℝ := S * S * A * C
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro x
  have hw : 0 ≤ C * equilibriumDensityDerivativeWeight β n x :=
    mul_nonneg hC.le (equilibriumDensityDerivativeWeight_nonneg β n x)
  have hp : ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun y => a y * R.density y) x‖ ≤
      S * A * (C * equilibriumDensityDerivativeWeight β n x) := by
    intro j hj
    exact equilibrium_iteratedFDeriv_mul_bound hasmooth R.smooth hj hA hw x
      (fun i hi => habound i hi x) (fun i hi => hprior i hi x)
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  have h := equilibrium_iteratedFDeriv_smul_bound (hasmooth.mul R.smooth)
    (innerSL ℝ).contDiff (n := n) le_rfl (mul_nonneg (mul_nonneg hS hA) hw)
    (by positivity : 0 ≤ 1 + ‖x‖) x hp
    (fun j _ => equilibrium_iteratedFDeriv_innerSL_norm_le j x)
  apply h.trans_eq
  rw [equilibriumDensityDerivativeWeight_succ]
  dsimp only [B]
  ring

/-- Every finite derivative order of the constructed thermal equilibrium has
the manuscript Gaussian-polynomial tail. No regularity or derivative-tail
hypothesis is added to the constructed reference. -/
theorem equilibriumReference_allDerivative_tails {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ n, ∀ x : ℂ,
      ‖iteratedFDeriv ℝ j R.density x‖ ≤ C * equilibriumDensityDerivativeWeight β n x := by
  induction n with
  | zero =>
      refine ⟨R.tailConstant, R.tailConstant_pos, ?_⟩
      intro j hj x
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (R.positive x)]
      have he : -(β / 2) * ‖x‖ ^ 2 = -β * ‖x‖ ^ 2 / 2 := by ring
      simpa only [equilibriumDensityDerivativeWeight, equilibriumPolynomialGaussian,
        Nat.cast_zero, add_zero, he, mul_assoc] using R.tail x
  | succ n ih =>
      obtain ⟨C, hC, hprior⟩ := ih
      obtain ⟨B, hB, hnext⟩ := equilibriumReference_derivative_tail_step hβ R n hC hprior
      refine ⟨C + B, add_pos_of_pos_of_nonneg hC hB, ?_⟩
      intro j hj x
      by_cases hjn : j ≤ n
      · apply (hprior j hjn x).trans
        exact (mul_le_mul_of_nonneg_left (equilibriumDensityDerivativeWeight_le_succ β n x) hC.le).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB)
            (equilibriumDensityDerivativeWeight_nonneg β (n + 1) x))
      · have hje : j = n + 1 := by omega
        subst j
        exact (hnext x).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le)
          (equilibriumDensityDerivativeWeight_nonneg β (n + 1) x))

/-- Exact physical n-th derivative tail, stated without an auxiliary weight. -/
theorem equilibriumReference_iteratedFDeriv_tail {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ, ‖iteratedFDeriv ℝ n R.density x‖ ≤
      C * (1 + ‖x‖) ^ (β + (n : ℝ)) * Real.exp (-β * ‖x‖ ^ 2 / 2) := by
  obtain ⟨C, hC, h⟩ := equilibriumReference_allDerivative_tails hβ R n
  refine ⟨C, hC, ?_⟩
  intro x
  have he : -(β / 2) * ‖x‖ ^ 2 = -β * ‖x‖ ^ 2 / 2 := by ring
  simpa only [equilibriumDensityDerivativeWeight, equilibriumPolynomialGaussian, he, mul_assoc]
    using h n le_rfl x

end RepulsiveCoulomb
