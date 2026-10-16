import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryOriginalGraph
import LeanResearch.RepulsiveCoulomb.DbarBranchDistributionCompatibility

/-! The closed raw compatibility space K={g:curl(Sg)=0 distributionally}.
Its equations are continuous compact pairings on auxiliary L2. The actual
minimal range and original transformed data lie in K, and its orthogonal
projection preserves the genuine adjoint graph and value. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology LinearPMap
namespace RepulsiveCoulomb

def coulombAuxiliaryCurlConstraintL {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →L[ℂ] ℂ :=
  (1 / 2 : ℂ) •
    (coulombAuxiliaryRawPairingL hβ j (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) +
      Complex.I • coulombAuxiliaryRawPairingL hβ j
        (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ) -
      coulombAuxiliaryRawPairingL hβ i (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N j 1) φ) -
      Complex.I • coulombAuxiliaryRawPairingL hβ i
        (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N j Complex.I) φ))

theorem coulombAuxiliaryCurlConstraintL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombAuxiliaryCurlConstraintL hβ i j φ g = (1 / 2 : ℂ) *
      (coulombAuxiliaryRawPairingL hβ j (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) g +
      Complex.I * coulombAuxiliaryRawPairingL hβ j
        (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ) g -
      coulombAuxiliaryRawPairingL hβ i (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N j 1) φ) g -
      Complex.I * coulombAuxiliaryRawPairingL hβ i
        (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N j Complex.I) φ) g) := by
  simp only [coulombAuxiliaryCurlConstraintL, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]

def coulombAuxiliaryCompatibilitySubmodule (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Submodule ℂ (Lp (CoulombConfig N) 2 (coulombMeasure N β)) where
  carrier := {g | ∀ i j φ, coulombAuxiliaryCurlConstraintL hβ i j φ g = 0}
  zero_mem' := by intro i j φ; exact map_zero _
  add_mem' := by
    intro f g hf hg i j φ
    rw [map_add, hf i j φ, hg i j φ, add_zero]
  smul_mem' := by
    intro c f hf i j φ
    rw [map_smul, hf i j φ, smul_zero]

theorem coulombAuxiliaryCompatibilitySubmodule_isClosed (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsClosed (coulombAuxiliaryCompatibilitySubmodule N hβ :
      Set (Lp (CoulombConfig N) 2 (coulombMeasure N β))) := by
  change IsClosed {g | ∀ i j φ, coulombAuxiliaryCurlConstraintL hβ i j φ g = 0}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro φ
  exact isClosed_eq (coulombAuxiliaryCurlConstraintL hβ i j φ).continuous continuous_const

def coulombAuxiliaryCompatibility (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ClosedSubmodule ℂ (Lp (CoulombConfig N) 2 (coulombMeasure N β)) :=
  ⟨coulombAuxiliaryCompatibilitySubmodule N hβ, coulombAuxiliaryCompatibilitySubmodule_isClosed N hβ⟩

theorem coulombAuxiliaryCurlConstraint_original_output {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (g q : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hraw : q =ᵐ[coulombMeasure N β]
      fun z => dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z))
    (i j : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryCurlConstraintL hβ i j φ g =
      -(coulombDistributionDbarCoordinateL N i
        (coulombL2Distribution hβ ((coulombCoordinate j).compLpL 2 (coulombMeasure N β) q)) φ) +
      coulombDistributionDbarCoordinateL N j
        (coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) q)) φ := by
  rw [coulombAuxiliaryCurlConstraintL_apply]
  simp_rw [coulombAuxiliaryRawPairing_original_output hβ g q hraw,
    coulombDistributionDbarCoordinateL_apply]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem coulombAuxiliary_original_datum_mem_compatibility {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {q : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, q) ∈ coulombMaxDbarGraph hβ) :
    coulombInverseRootL2L N β q ∈ coulombAuxiliaryCompatibility N hβ := by
  intro i j φ
  rw [coulombAuxiliaryCurlConstraint_original_output hβ _ q (coulombInverseRootL2_raw_identity β q)]
  rw [coulombMaxDbarGraph_distribution_compatible hβ hfg i j, neg_add_cancel]

theorem coulombAuxiliaryCore_mem_compatibility {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombAuxiliaryCoreDerivativeL N hβ φ ∈ coulombAuxiliaryCompatibility N hβ := by
  change coulombInverseRootL2L N β (coulombComplexDbarCoreLinear N hβ φ) ∈ _
  rw [coulombComplexDbarCoreLinear_apply]
  exact coulombAuxiliary_original_datum_mem_compatibility hβ (coulombComplexCore_mem_maxDbarGraph hβ φ)

theorem coulombAuxiliaryMinimalGraph_output_mem_compatibility {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {J : CoulombDbarL2Pair N β} (hJ : J ∈ coulombAuxiliaryMinimalGraph N hβ) :
    J.2 ∈ coulombAuxiliaryCompatibility N hβ := by
  have hc : IsClosed ((fun J : CoulombDbarL2Pair N β => J.2) ⁻¹'
      (coulombAuxiliaryCompatibility N hβ : Set _)) :=
    (coulombAuxiliaryCompatibility N hβ).isClosed.preimage continuous_snd
  change J ∈ (coulombAuxiliaryMinimalGraph N hβ : Set _) at hJ
  rw [coulombAuxiliaryMinimalGraph_coe] at hJ
  apply (closure_minimal (s := range (coulombAuxiliaryCoreJetLinear N hβ)) _ hc) hJ
  rintro _ ⟨φ, rfl⟩
  exact coulombAuxiliaryCore_mem_compatibility hβ φ

theorem coulombAuxiliaryCompatibility_orthogonal_adjoint_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hg : g ∈ (coulombAuxiliaryCompatibility N hβ).toSubmodule.orthogonal) :
    (g, 0) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph := by
  apply (coulombAuxiliaryDbarAdjoint_graph_iff hβ g 0).mpr
  intro φ
  rw [inner_zero_right]
  exact hg (coulombAuxiliaryCoreDerivativeL N hβ φ) (coulombAuxiliaryCore_mem_compatibility hβ φ)

def coulombAuxiliaryCompatibilityProjection (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →L[ℂ]
      Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombAuxiliaryCompatibility N hβ).toSubmodule.starProjection

theorem coulombAuxiliaryCompatibilityProjection_adjoint_graph {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (hgh : (g, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph) :
    (coulombAuxiliaryCompatibilityProjection N hβ g, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph := by
  have hperp : g - coulombAuxiliaryCompatibilityProjection N hβ g ∈
      (coulombAuxiliaryCompatibility N hβ).toSubmodule.orthogonal :=
    Submodule.sub_starProjection_mem_orthogonal g
  have hz := coulombAuxiliaryCompatibility_orthogonal_adjoint_zero hβ hperp
  simpa only [Prod.mk_sub_mk, sub_sub_cancel, sub_zero] using
    (coulombAuxiliaryDbarAdjoint N hβ).graph.sub_mem hgh hz

theorem coulombAuxiliaryCompatibilityProjection_datum_pairing {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {d : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hd : d ∈ coulombAuxiliaryCompatibility N hβ)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    inner ℂ d g = inner ℂ d (coulombAuxiliaryCompatibilityProjection N hβ g) := by
  have hperp : g - coulombAuxiliaryCompatibilityProjection N hβ g ∈
      (coulombAuxiliaryCompatibility N hβ).toSubmodule.orthogonal :=
    Submodule.sub_starProjection_mem_orthogonal g
  have h := hperp d hd
  rw [inner_sub_right] at h
  exact sub_eq_zero.mp h

end RepulsiveCoulomb
