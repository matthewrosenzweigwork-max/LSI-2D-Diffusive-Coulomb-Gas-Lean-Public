import LeanResearch.RepulsiveCoulomb.PoleBranchSymmetricProjectionDistance
import LeanResearch.RepulsiveCoulomb.PoleBranchRealComplexCenter
import LeanResearch.RepulsiveCoulomb.PoleBranchSymmetricCoreClosure
import LeanResearch.RepulsiveCoulomb.CoulombDbarCore

/-! Conditional assembly of the canonical symmetric Poincare argument.
The original-core dbar projection-distance estimate is an explicit, still-open
premise. No theorem here supplies that estimate or completes Theorem 1.1.
The endpoint beta/N=2, every N, physical factor 1/beta, and original full
closed form are retained. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
namespace RepulsiveCoulomb

theorem poleBranch_real_core_complex_value {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Complex.ofRealCLM.compLpL 2 (coulombMeasure N β)
      (coulombFormValueL N hβ (coulombFormCore hβ φ)) =
        coulombComplexCoreValue hβ (TestFunction.postcompCLM Complex.ofRealCLM φ) := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (coulombFormValueL N hβ (coulombFormCore hβ φ)),
    coulombFormCore_value hβ φ,
    coulombComplexCoreValue_coe hβ (TestFunction.postcompCLM Complex.ofRealCLM φ)] with z he hv hc
  rw [he, hv, hc]
  rfl

theorem poleBranch_real_core_dbar_norm_sq {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ‖coulombComplexCoreDbar hβ (TestFunction.postcompCLM Complex.ofRealCLM φ)‖ ^ 2 =
      (1 / 4 : ℝ) * coulombFormEnergy N hβ (coulombFormCore hβ φ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ z, ‖coulombDbar (fun x => (φ x : ℂ)) z‖ ^ 2 ∂coulombMeasure N β := by
      apply integral_congr_ae
      filter_upwards [coulombComplexCoreDbar_coe hβ
        (TestFunction.postcompCLM Complex.ofRealCLM φ)] with z hz
      rw [hz, real_inner_self_eq_norm_sq]
      rfl
    _ = _ := coulombDbar_real_core_energy hβ φ

theorem poleBranch_real_core_value_invariant {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hsym : ∀ (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N), φ (coulombPermute σ z) = φ z) :
    ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ (coulombFormCore hβ φ)) =
        coulombFormValueL N hβ (coulombFormCore hβ φ) := by
  intro σ
  have ht := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae
    (coulombFormCore_value hβ φ)
  apply Lp.ext
  filter_upwards [coulombValuePermuteL_coe N hβ σ (coulombFormValueL N hβ (coulombFormCore hβ φ)),
    ht, coulombFormCore_value hβ φ] with z hp ht hv
  rw [hp, ht, hv, hsym σ z]

/-- This is an implication from the original-core distance estimate, not a proof of it. -/
theorem poleBranch_symmetric_core_pi_of_dbar_distance {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    (hdist : ∀ ψ : TestFunction (coulombDomain N) ℂ ⊤,
      ‖coulombComplexCoreValue hβ ψ -
        coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ)‖ ^ 2 ≤
          (2 / β) * ‖coulombComplexCoreDbar hβ ψ‖ ^ 2)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hsym : ∀ (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N), φ (coulombPermute σ z) = φ z) :
    variance (φ : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (1 / β) * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) := by
  let vR := coulombFormValueL N hβ (coulombFormCore hβ φ)
  let ψ : TestFunction (coulombDomain N) ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
  let f₀ := Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ vR)
  have hsymR := poleBranch_real_core_value_invariant hβ φ hsym
  have hfreal : poleBranchComplexConj N β f₀ = f₀ := poleBranch_ofRealLp_conjugate _
  have hfmean : poleBranchComplexMean N hβ f₀ = 0 := poleBranch_ofRealLp_center_mean hβ vR
  have hfsym : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ f₀ = f₀ := by
    intro σ
    change poleBranchComplexPermute N hβ σ
      (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ vR)) = _
    rw [poleBranch_ofRealLp_permute, poleBranchRealCenter_permute hβ vR hsymR σ]
  have hvar : ‖f₀‖ ^ 2 = variance (φ : CoulombConfig N → ℝ) (coulombMeasure N β) :=
    (poleBranch_ofRealLp_center_norm_sq hβ vR).trans (variance_congr (coulombFormCore_value hβ φ))
  have hres : f₀ - coulombDbarWeakProjection N hβ f₀ =
      coulombComplexCoreValue hβ ψ - coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ) := by
    change Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ vR) -
      coulombDbarWeakProjection N hβ
        (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ vR)) = _
    simp only [poleBranch_ofRealLp_center]
    rw [poleBranch_projection_centered_residual]
    exact congrArg (fun v => v - coulombDbarWeakProjection N hβ v)
      (poleBranch_real_core_complex_value hβ φ)
  calc
    _ = ‖f₀‖ ^ 2 := hvar.symm
    _ ≤ 2 * ‖f₀ - coulombDbarWeakProjection N hβ f₀‖ ^ 2 :=
      poleBranch_symmetric_projection_distance hβ ha2 f₀ hfreal hfmean hfsym
    _ = 2 * ‖coulombComplexCoreValue hβ ψ -
        coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ)‖ ^ 2 := by rw [hres]
    _ ≤ 2 * ((2 / β) * ‖coulombComplexCoreDbar hβ ψ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hdist ψ) (by norm_num)
    _ = (1 / β) * coulombFormEnergy N hβ (coulombFormCore hβ φ) := by
      change 2 * ((2 / β) * ‖coulombComplexCoreDbar hβ
        (TestFunction.postcompCLM Complex.ofRealCLM φ)‖ ^ 2) = _
      rw [poleBranch_real_core_dbar_norm_sq]
      ring
    _ = _ := by rw [coulombFormCore_energy_eq_integral]

/-- Exact original full-domain implication, retaining the open dbar premise. -/
theorem poleBranch_symmetric_form_pi_of_dbar_distance {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    (hdist : ∀ ψ : TestFunction (coulombDomain N) ℂ ⊤,
      ‖coulombComplexCoreValue hβ ψ -
        coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ)‖ ^ 2 ≤
          (2 / β) * ‖coulombComplexCoreDbar hβ ψ‖ ^ 2)
    (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (1 / β) * coulombFormEnergy N hβ u :=
  poleBranch_symmetric_form_poincare_of_core hβ
    (poleBranch_symmetric_core_pi_of_dbar_distance hβ ha2 hdist) u hsym


/-- Application to the actual symmetrizer, still conditional on the same open
original-core dbar estimate. The energy is that of the original full-domain input. -/
theorem poleBranch_symmetrized_form_pi_of_dbar_distance {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    (hdist : ∀ ψ : TestFunction (coulombDomain N) ℂ ⊤,
      ‖coulombComplexCoreValue hβ ψ -
        coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ ψ)‖ ^ 2 ≤
          (2 / β) * ‖coulombComplexCoreDbar hβ ψ‖ ^ 2)
    (u : CoulombFormDomain N hβ) :
    variance (coulombSymmetrizer N hβ (coulombFormValueL N hβ u) : CoulombConfig N → ℝ)
      (coulombMeasure N β) ≤ (1 / β) * coulombFormEnergy N hβ u := by
  have hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ
          (coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u)) =
        coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u) := by
    intro σ
    rw [coulombFormSymmetrizer_value]
    exact coulombSymmetrizer_invariant N hβ σ _
  have H := poleBranch_symmetric_form_pi_of_dbar_distance hβ ha2 hdist
    (coulombFormSymmetrizer N hβ u) hsym
  rw [coulombFormSymmetrizer_value] at H
  exact H.trans (mul_le_mul_of_nonneg_left (coulombFormSymmetrizer_energy_le N hβ u)
    (by positivity))

end RepulsiveCoulomb
