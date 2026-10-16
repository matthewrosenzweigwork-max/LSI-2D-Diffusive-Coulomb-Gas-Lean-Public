import LeanResearch.RepulsiveCoulomb.EquilibriumBranchWeightedRadialOperator

/-! All-order global derivative bounds for radial averaging. The induction
uses the actual first derivative identity A_k' f=A_(k+1)(Df) and the pinned
isometric currying norm identity; no unproved iterated-integral interchange
is assumed. Bounds through order n for f give the same bound at order n for
its weighted average. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Weighted radial averaging preserves each supplied finite-order global
Fréchet derivative bound. The statement is Banach-valued so the induction
applies to actual derivative-valued functions. -/
theorem equilibriumWeightedRadialOperator_iteratedFDeriv_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (n k : ℕ) {f : ℂ → V} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (D : ℕ → ℝ) (hD0 : ∀ j ≤ n, 0 ≤ D j)
    (hD : ∀ j ≤ n, ∀ x : ℂ, ‖iteratedFDeriv ℝ j f x‖ ≤ D j) (x : ℂ) :
    ‖iteratedFDeriv ℝ n (equilibriumWeightedRadialOperator k f) x‖ ≤ D n := by
  induction n generalizing V k f D x with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      apply equilibriumWeightedRadialOperator_norm_le k (hD0 0 le_rfl)
      intro y
      simpa only [norm_iteratedFDeriv_zero] using hD 0 le_rfl y
  | succ n ih =>
      have h0 : 0 ≤ D 0 := hD0 0 (Nat.zero_le _)
      have h1 : 0 ≤ D 1 := hD0 1 (by omega)
      have hf0 : ∀ y : ℂ, ‖f y‖ ≤ D 0 := by
        intro y
        simpa only [norm_iteratedFDeriv_zero] using hD 0 (Nat.zero_le _) y
      have hf1 : ∀ y : ℂ, ‖fderiv ℝ f y‖ ≤ D 1 := by
        intro y
        simpa only [norm_iteratedFDeriv_one] using hD 1 (by omega) y
      have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
      have hD0' : ∀ j ≤ n, 0 ≤ D (j + 1) := fun j hj => hD0 (j + 1) (Nat.succ_le_succ hj)
      have hD' : ∀ j ≤ n, ∀ y : ℂ, ‖iteratedFDeriv ℝ j (fderiv ℝ f) y‖ ≤ D (j + 1) := by
        intro j hj y
        rw [norm_iteratedFDeriv_fderiv]
        exact hD (j + 1) (Nat.succ_le_succ hj) y
      rw [← norm_iteratedFDeriv_fderiv,
        equilibriumWeightedRadialOperator_fderiv k hf h0 h1 hf0 hf1]
      exact ih (k + 1) hfd (fun j => D (j + 1)) hD0' hD' x

/-- The scalar radial average J inherits the actual all-order bounds. -/
theorem equilibriumRadialAverage_iteratedFDeriv_norm_le (n : ℕ) {ρ : ℂ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (D : ℕ → ℝ) (hD0 : ∀ j ≤ n, 0 ≤ D j)
    (hD : ∀ j ≤ n, ∀ x : ℂ, ‖iteratedFDeriv ℝ j ρ x‖ ≤ D j) (x : ℂ) :
    ‖iteratedFDeriv ℝ n (equilibriumRadialAverage ρ) x‖ ≤ D n := by
  rw [← equilibriumWeightedRadialOperator_one ρ]
  exact equilibriumWeightedRadialOperator_iteratedFDeriv_norm_le n 1 hρ D hD0 hD x

end RepulsiveCoulomb
