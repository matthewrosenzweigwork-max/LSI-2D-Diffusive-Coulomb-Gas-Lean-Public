module

public import LeanResearch.RepulsiveCoulomb.DbarBranchProjectionDistance
public import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalSymmetricPI
public import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalSymmetricCompact
public import LeanResearch.RepulsiveCoulomb.CoulombAssociatedConstants

@[expose] public section

/-! Original-paper analytic instances on the literal normalized Gibbs measure.
The Euclidean maximal dbar graph, holomorphic kernel, collision removal,
common-phase identity, compact resolvent, and compact-temperature gap are
proved source instances; none is an analytic certificate premise here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory InnerProductSpace
namespace RepulsiveCoulomb.PaperRoute

/-- Demailly's required exact-data instance in the original Euclidean norms. -/
theorem paper_dbar_graph_distance {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)}
    {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombMaxDbarGraph hβ) :
    ‖f - coulombDbarWeakProjection N hβ f‖ ^ 2 ≤ (2 / β) * ‖g‖ ^ 2 :=
  coulombDbarWeakProjection_distance_sq_le hβ hfg

theorem paper_dbar_core_distance {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    ‖coulombComplexCoreValue hβ φ -
      coulombDbarWeakProjection N hβ (coulombComplexCoreValue hβ φ)‖ ^ 2 ≤
        (2 / β) * ‖coulombComplexCoreDbar hβ φ‖ ^ 2 :=
  paper_dbar_graph_distance hβ (coulombComplexCore_mem_maxDbarGraph hβ φ)

theorem paper_dbar_kernel_holomorphic {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    f ∈ coulombDbarWeakKernel N hβ ↔
      ∃ h : CoulombConfig N → ℂ, DifferentiableOn ℂ h (coulombDomain N) ∧
        f =ᵐ[coulombMeasure N β] h :=
  coulombDbarWeakKernel_mem_iff_holomorphic hβ f

/-- At-most-simple pole, parity removal and Hartogs include the exponent-two endpoint. -/
theorem paper_symmetric_holomorphic_removal {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    {f : CoulombConfig N → ℂ} (hf : DifferentiableOn ℂ f (coulombDomain N))
    (hi : MemLp f 2 (coulombMeasure N β))
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      (fun z => f (coulombPermute σ z)) =ᵐ[coulombMeasure N β] f) :
    ∃ F : CoulombConfig N → ℂ, Differentiable ℂ F ∧ EqOn F f (coulombDomain N) :=
  poleBranch_coulomb_weighted_symmetric_removable hβ ha2 hf hi hsym

theorem paper_common_phase_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F G : CoulombConfig N → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFG : Integrable (fun z => F z * G z) (coulombMeasure N β)) :
    (∫ z, F z * G z ∂coulombMeasure N β) = F 0 * G 0 :=
  coulomb_common_phase_bilinear hβ hF hG hFG

theorem paper_real_dbar_physical_energy {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ‖coulombComplexCoreDbar hβ (TestFunction.postcompCLM Complex.ofRealCLM φ)‖ ^ 2 =
      (1 / 4 : ℝ) * coulombFormEnergy N hβ (coulombFormCore hβ φ) :=
  poleBranch_real_core_dbar_norm_sq hβ φ

theorem paper_symmetric_poincare_small_exponent {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (1 / β) * coulombFormEnergy N hβ u :=
  poleBranch_symmetric_form_pi_of_dbar_distance hβ ha2 (paper_dbar_core_distance hβ) u hsym

/-- Compactness of the original full closed-form embedding, not just a gap witness. -/
theorem paper_fixed_particle_form_compact (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsCompactOperator (coulombFormValueL N hβ) :=
  coulombFormValueL_isCompactOperator N hβ

theorem paper_fixed_particle_resolvent_compact (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsCompactOperator (coulombFormResolvent N hβ) :=
  coulombFormResolvent_isCompactOperator N hβ

theorem paper_fixed_particle_operator_selfAdjoint (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsSelfAdjoint (coulombAssociatedOperator N hβ) :=
  coulombAssociatedOperator_selfAdjoint N hβ

theorem paper_fixed_particle_operator_nonneg (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : (coulombAssociatedOperator N hβ).domain) :
    0 ≤ inner ℝ (coulombAssociatedOperator N hβ u) (u : Lp ℝ 2 (coulombMeasure N β)) :=
  coulombAssociatedOperator_nonneg N hβ u

/-- The unbounded graph is associated with the original physical closed form. -/
theorem paper_fixed_particle_variational_association {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (x g : Lp ℝ 2 (coulombMeasure N β)) :
    (x, g) ∈ coulombAssociatedGraph N hβ ↔
      ∃ u : CoulombFormDomain N hβ, coulombFormValueL N hβ u = x ∧
        ∀ v : CoulombFormDomain N hβ,
          coulombFormEnergyPair N hβ u v = inner ℝ g (coulombFormValueL N hβ v) :=
  coulombAssociatedGraph_variational hβ x g

theorem paper_fixed_particle_resolvent_left_inverse (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : (coulombAssociatedOperator N hβ).domain) :
    coulombFormResolvent N hβ ((u : Lp ℝ 2 (coulombMeasure N β)) +
      coulombAssociatedOperator N hβ u) = u :=
  coulombFormResolvent_left_inverse N hβ u

theorem paper_fixed_particle_resolvent_right_inverse (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β)) :
    ∃ u : (coulombAssociatedOperator N hβ).domain,
      (u : Lp ℝ 2 (coulombMeasure N β)) = coulombFormResolvent N hβ f ∧
      (u : Lp ℝ 2 (coulombMeasure N β)) + coulombAssociatedOperator N hβ u = f :=
  coulombFormResolvent_right_inverse N hβ f

theorem paper_fixed_particle_kernel_constants (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : (coulombAssociatedOperator N hβ).domain)
    (hu : coulombAssociatedOperator N hβ u = 0) :
    ∃ a : ℝ, (u : Lp ℝ 2 (coulombMeasure N β)) =ᵐ[coulombMeasure N β] fun _ => a :=
  coulombAssociatedOperator_zero_constant N hβ u hu

theorem paper_fixed_particle_constants_kernel (N : ℕ) {β : ℝ} (hβ : 0 < β) (a : ℝ) :
    ∃ u : (coulombAssociatedOperator (N + 2) hβ).domain,
      (u : Lp ℝ 2 (coulombMeasure (N + 2) β)) = a • poleBranchRealOne (N + 2) hβ ∧
      coulombAssociatedOperator (N + 2) hβ u = 0 :=
  coulombAssociatedOperator_constant_zero N hβ a

theorem paper_fixed_particle_poincare (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoulombFormDomain (N + 2) hβ,
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤ C * coulombFormEnergy (N + 2) hβ u :=
  coulomb_fixed_particle_poincare N hβ

/-- One genuine fixed-N bound on each compact positive temperature interval. -/
theorem paper_fixed_particle_compact_temperature (N : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : β ∈ Set.Icc a b),
      ∀ u : CoulombFormDomain (N + 2) (ha.trans_le hβ.1),
        variance (coulombFormValueL (N + 2) (ha.trans_le hβ.1) u :
          CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) ≤
        C * coulombFormEnergy (N + 2) (ha.trans_le hβ.1) u :=
  coulomb_compact_temperature_poincare N ha hab

/-- The exact Csym includes the actual optimal gaps of the finite exceptional family. -/
theorem paper_symmetric_poincare {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      poleBranchSymmetricPoincareConstant hβ * coulombFormEnergy N hβ u :=
  poleBranch_optimal_symmetric_pi_of_dbar_distance hN hβ
    (paper_dbar_core_distance hβ) u hsym

theorem paper_symmetrized_poincare {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    variance (coulombSymmetrizer N hβ (coulombFormValueL N hβ u) : CoulombConfig N → ℝ)
      (coulombMeasure N β) ≤
      poleBranchSymmetricPoincareConstant hβ * coulombFormEnergy N hβ u :=
  poleBranch_optimal_symmetrized_pi_of_dbar_distance hN hβ
    (paper_dbar_core_distance hβ) u

end RepulsiveCoulomb.PaperRoute
