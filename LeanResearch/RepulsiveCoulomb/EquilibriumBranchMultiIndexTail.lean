import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityDerivativeTail

/-! The literal Cartesian multi-index tail in eq:mu-tail. The partial
operators below are actual successive Fréchet derivatives in the real unit
coordinate directions 1 and I. Their identification with evaluation of the
full derivative is proved, so the multi-index conclusion is not merely a
renaming of an operator-norm bound. All orders, including zero, are covered. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

/-- Successive actual directional derivatives, in the displayed order. -/
def equilibriumOrderedDirectionalDerivative :
    (n : ℕ) → (Fin n → ℂ) → (ℂ → ℝ) → ℂ → ℝ
  | 0, _, f => f
  | n + 1, v, f => fun x =>
      fderiv ℝ (equilibriumOrderedDirectionalDerivative n (Fin.tail v) f) x (v 0)

/-- Smoothness identifies the recursive directional derivatives with the
actual full Fréchet derivative evaluated on the direction tuple. -/
theorem equilibriumOrderedDirectionalDerivative_eq_iteratedFDeriv
    {f : ℂ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (n : ℕ) (v : Fin n → ℂ) (x : ℂ) :
    equilibriumOrderedDirectionalDerivative n v f x = iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have he : equilibriumOrderedDirectionalDerivative n (Fin.tail v) f =
          fun y => iteratedFDeriv ℝ n f y (Fin.tail v) := funext (ih (Fin.tail v))
      simp only [equilibriumOrderedDirectionalDerivative, he]
      have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
        hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
      exact (hd x).iteratedFDeriv_succ_apply_left'.symm

/-- The direction word for alpha=(alpha_0,alpha_1): alpha_0 copies of the real
unit vector, followed by alpha_1 copies of the imaginary unit vector. -/
def equilibriumMultiIndexDirections (α : Fin 2 → ℕ) : Fin (α 0 + α 1) → ℂ :=
  fun i => if i.val < α 0 then 1 else Complex.I

/-- The actual Cartesian partial derivative partial^(alpha_0,alpha_1). -/
def equilibriumMultiIndexDerivative (α : Fin 2 → ℕ) (f : ℂ → ℝ) : ℂ → ℝ :=
  equilibriumOrderedDirectionalDerivative (α 0 + α 1) (equilibriumMultiIndexDirections α) f

theorem equilibriumMultiIndexDirections_norm (α : Fin 2 → ℕ) (i : Fin (α 0 + α 1)) :
    ‖equilibriumMultiIndexDirections α i‖ = 1 := by
  unfold equilibriumMultiIndexDirections
  split_ifs <;> simp

/-- Every Cartesian partial derivative is controlled by the full physical
Fréchet derivative of the same order, with no dimension-dependent rescaling. -/
theorem equilibriumMultiIndexDerivative_norm_le {f : ℂ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (α : Fin 2 → ℕ) (x : ℂ) :
    |equilibriumMultiIndexDerivative α f x| ≤ ‖iteratedFDeriv ℝ (α 0 + α 1) f x‖ := by
  rw [equilibriumMultiIndexDerivative, equilibriumOrderedDirectionalDerivative_eq_iteratedFDeriv hf]
  simpa only [Real.norm_eq_abs, equilibriumMultiIndexDirections_norm,
    Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ (α 0 + α 1) f x).le_opNorm (equilibriumMultiIndexDirections α)

/-- Manuscript eq:mu-tail for every actual constructed reference and every
multi-index. Its polynomial exponent is exactly beta+|alpha|. -/
theorem equilibriumReference_multiIndex_tail {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (α : Fin 2 → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ,
      |equilibriumMultiIndexDerivative α R.density x| ≤
        C * (1 + ‖x‖) ^ (β + ((α 0 + α 1 : ℕ) : ℝ)) *
          Real.exp (-β * ‖x‖ ^ 2 / 2) := by
  obtain ⟨C, hC, htail⟩ := equilibriumReference_iteratedFDeriv_tail hβ R (α 0 + α 1)
  exact ⟨C, hC, fun x => (equilibriumMultiIndexDerivative_norm_le R.smooth α x).trans (htail x)⟩

/-- The literal selected thermal equilibrium endpoint; no reference package,
smoothness assumption, or derivative-tail assumption remains an input. -/
theorem equilibriumConstructedReference_multiIndex_tail {β : ℝ} (hβ : 0 < β)
    (α : Fin 2 → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℂ,
      |equilibriumMultiIndexDerivative α (equilibriumConstructedReference β hβ).density x| ≤
        C * (1 + ‖x‖) ^ (β + ((α 0 + α 1 : ℕ) : ℝ)) *
          Real.exp (-β * ‖x‖ ^ 2 / 2) :=
  equilibriumReference_multiIndex_tail hβ (equilibriumConstructedReference β hβ) α

end RepulsiveCoulomb
