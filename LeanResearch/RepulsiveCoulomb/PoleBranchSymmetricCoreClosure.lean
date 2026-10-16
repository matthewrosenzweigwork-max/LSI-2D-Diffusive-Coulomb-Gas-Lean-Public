import LeanResearch.RepulsiveCoulomb.PoleBranchRealLpMean
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Symmetrization preserves the original real compact smooth collision-free
core. Every symmetric element of the original closed physical form has a
symmetric-core approximation. The final theorem is only the exact closure
implication; its core Poincare premise must be supplied separately. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def poleBranchFormCoreLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℝ ⊤ →ₗ[ℝ] CoulombFormDomain N hβ where
  toFun := coulombFormCore hβ
  map_add' φ ψ := Subtype.ext (coulombCoreJet_add hβ φ ψ)
  map_smul' c φ := Subtype.ext (coulombCoreJet_smul hβ c φ)

def poleBranchCoreSymmetrizer {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : TestFunction (coulombDomain N) ℝ ⊤ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin N), coulombPermuteCore σ φ

theorem poleBranchCoreSymmetrizer_form {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormCore hβ (poleBranchCoreSymmetrizer φ) =
      coulombFormSymmetrizer N hβ (coulombFormCore hβ φ) := by
  rw [coulombFormSymmetrizer_apply]
  change poleBranchFormCoreLinear N hβ
    ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), coulombPermuteCore σ φ) = _
  rw [map_smul, map_sum]
  simp only [poleBranchFormCoreLinear, LinearMap.coe_mk, AddHom.coe_mk,
    coulombFormPermuteL_core]

theorem poleBranch_core_pointwise_invariant_of_value {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ (coulombFormCore hβ φ)) =
        coulombFormValueL N hβ (coulombFormCore hβ φ)) :
    ∀ (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N), φ (coulombPermute σ z) = φ z := by
  intro σ
  have hv := coulombFormCore_value hβ φ
  have hp := coulombValuePermuteL_coe N hβ σ (coulombFormValueL N hβ (coulombFormCore hβ φ))
  rw [hsym σ] at hp
  have ht : (fun z => coulombFormValueL N hβ (coulombFormCore hβ φ) (coulombPermute σ z))
      =ᵐ[coulombMeasure N β] (fun z => φ (coulombPermute σ z)) :=
    (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae_eq_comp hv
  have hae : (fun z => φ (coulombPermute σ z)) =ᵐ[coulombMeasure N β] φ := by
    filter_upwards [ht, hp, hv] with z ht hp hv
    exact ht.symm.trans (hp.symm.trans hv)
  have he := Measure.eq_of_ae_eq ((coulombMeasure_ae_iff hβ).mp hae)
    (φ.continuous.comp (coulombPermute σ).continuous) φ.continuous
  exact congrFun he

theorem poleBranchCoreSymmetrizer_invariant {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ∀ (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N),
      poleBranchCoreSymmetrizer φ (coulombPermute σ z) = poleBranchCoreSymmetrizer φ z := by
  apply poleBranch_core_pointwise_invariant_of_value hβ
  intro σ
  rw [poleBranchCoreSymmetrizer_form, coulombFormSymmetrizer_value]
  exact coulombSymmetrizer_invariant N hβ σ _

theorem poleBranchSymmetrizer_eq_self {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β))
    (hsym : ∀ σ : Equiv.Perm (Fin N), coulombValuePermuteL N hβ σ v = v) :
    coulombSymmetrizer N hβ v = v := by
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [coulombSymmetrizer_apply]
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem poleBranchFormSymmetrizer_eq_self {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    coulombFormSymmetrizer N hβ u = u := by
  apply coulombFormValueL_injective N hβ
  rw [coulombFormSymmetrizer_value]
  exact poleBranchSymmetrizer_eq_self hβ _ hsym

theorem poleBranch_symmetric_core_approximation {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    ∃ φ : ℕ → TestFunction (coulombDomain N) ℝ ⊤,
      (∀ (n : ℕ) (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N),
        φ n (coulombPermute σ z) = φ n z) ∧
      Tendsto (fun n => coulombFormCore hβ (φ n)) atTop (𝓝 u) := by
  obtain ⟨ψ, hψ⟩ := coulombFormCore_approximation N hβ u
  refine ⟨fun n => poleBranchCoreSymmetrizer (ψ n),
    fun n => poleBranchCoreSymmetrizer_invariant hβ (ψ n), ?_⟩
  have hlim := ((coulombFormSymmetrizer N hβ).continuous.tendsto u).comp hψ
  change Tendsto (fun n => coulombFormSymmetrizer N hβ (coulombFormCore hβ (ψ n)))
    atTop (𝓝 (coulombFormSymmetrizer N hβ u)) at hlim
  simpa only [← poleBranchCoreSymmetrizer_form,
    poleBranchFormSymmetrizer_eq_self hβ u hsym] using hlim

/-- Exact original-domain closure; this does not prove its core inequality premise. -/
theorem poleBranch_symmetric_form_poincare_of_core {N : ℕ} {β C : ℝ} (hβ : 0 < β)
    (hcore : ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      (∀ (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N), φ (coulombPermute σ z) = φ z) →
      variance (φ : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
        C * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β))
    (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      C * coulombFormEnergy N hβ u := by
  obtain ⟨φ, hsymφ, hφ⟩ := poleBranch_symmetric_core_approximation hβ u hsym
  have hvar : Continuous (fun u : CoulombFormDomain N hβ =>
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β)) :=
    (poleBranchRealLp_variance_continuous hβ).comp (coulombFormValueL N hβ).continuous
  have henergy : Continuous (coulombFormEnergy N hβ) :=
    (coulombFormGradientL N hβ).continuous.norm.pow 2
  apply le_of_tendsto_of_tendsto ((hvar.tendsto u).comp hφ)
    (tendsto_const_nhds.mul ((henergy.tendsto u).comp hφ))
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply]
  rw [variance_congr (coulombFormCore_value hβ (φ n)), coulombFormCore_energy_eq_integral]
  exact hcore (φ n) (hsymφ n)

end RepulsiveCoulomb
