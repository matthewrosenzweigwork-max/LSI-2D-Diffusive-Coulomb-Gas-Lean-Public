import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryRawPairing

/-! Closure of the auxiliary core preserves the literal local weak dbar
relations. When its raw output Sg additionally belongs to the original
Euclidean weighted L2 space, the pair belongs to the checked original graph.
No global L2 assertion about Sg is made without that extra datum. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombAuxiliaryWeakConstraintL {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : CoulombDbarL2Pair N β →L[ℝ] ℂ :=
  ((coulombAuxiliaryRawPairingL hβ i φ).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _) +
    (1 / 2 : ℝ) •
      (((coulombL2TestPairingL hβ
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ)).comp
          (ContinuousLinearMap.fst ℝ _ _)) +
        ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp
          ((coulombL2TestPairingL hβ
            (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)).comp
            (ContinuousLinearMap.fst ℝ _ _))))

theorem coulombAuxiliaryWeakConstraintL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (J : CoulombDbarL2Pair N β) :
    coulombAuxiliaryWeakConstraintL hβ i φ J = coulombAuxiliaryRawPairingL hβ i φ J.2 +
      (1 / 2 : ℝ) •
        (coulombL2Distribution hβ J.1 (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) +
          Complex.I * coulombL2Distribution hβ J.1
            (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)) := by
  simp only [coulombAuxiliaryWeakConstraintL, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.id_apply,
    coulombL2TestPairingL_apply, smul_eq_mul]
  rfl

theorem coulombAuxiliaryMinimalGraph_weak {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {J : CoulombDbarL2Pair N β} (hJ : J ∈ coulombAuxiliaryMinimalGraph N hβ)
    (i : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryWeakConstraintL hβ i φ J = 0 := by
  have hc : IsClosed {J : CoulombDbarL2Pair N β | coulombAuxiliaryWeakConstraintL hβ i φ J = 0} :=
    isClosed_eq (coulombAuxiliaryWeakConstraintL hβ i φ).continuous continuous_const
  change J ∈ (coulombAuxiliaryMinimalGraph N hβ : Set _) at hJ
  rw [coulombAuxiliaryMinimalGraph_coe] at hJ
  apply (closure_minimal (s := range (coulombAuxiliaryCoreJetLinear N hβ)) _ hc) hJ
  rintro _ ⟨ψ, rfl⟩
  change coulombAuxiliaryWeakConstraintL hβ i φ
    (coulombComplexCoreValue hβ ψ, coulombAuxiliaryCoreDerivativeL N hβ ψ) = 0
  rw [coulombAuxiliaryWeakConstraintL_apply]
  change coulombAuxiliaryRawPairingL hβ i φ (coulombAuxiliaryCoreDerivativeL N hβ ψ) + _ = 0
  rw [coulombAuxiliaryRawPairing_core]
  exact (coulombWeakDbarConstraintL_apply hβ i φ
    (coulombComplexCoreValue hβ ψ, coulombComplexCoreDbar hβ ψ)).symm.trans
      (coulombComplexCore_mem_maxDbarGraph hβ ψ i φ)

theorem coulombAuxiliaryRawPairing_original_output {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (g q : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hraw : q =ᵐ[coulombMeasure N β]
      fun z => dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z))
    (i : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryRawPairingL hβ i φ g =
      coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) q) φ := by
  rw [coulombAuxiliaryRawPairingL_apply, coulombL2Distribution_apply]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mp hraw,
    (coulombMeasure_ae_iff hβ).mp
      ((coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) q)] with z hz hq
  rw [hq, hz]
  rfl

theorem coulombAuxiliaryMinimalGraph_original_graph {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {g q : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombAuxiliaryMinimalGraph N hβ)
    (hraw : q =ᵐ[coulombMeasure N β]
      fun z => dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z)) :
    (f, q) ∈ coulombMaxDbarGraph hβ := by
  intro i φ
  have h := coulombAuxiliaryMinimalGraph_weak hβ hfg i φ
  rw [coulombAuxiliaryWeakConstraintL_apply, coulombAuxiliaryRawPairing_original_output hβ g q hraw i φ] at h
  simpa only [coulombWeakDbarConstraintL_apply] using h

theorem coulombInverseRootL2_raw_identity {N : ℕ} (β : ℝ)
    (q : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    q =ᵐ[coulombMeasure N β] fun z =>
      dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (coulombInverseRootL2L N β q z) := by
  filter_upwards [coulombInverseRootL2_coe β q] with z hz
  change q z = dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (coulombInverseRootL2 β q z)
  rw [hz]
  exact (congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L (q z))
    (dbarGraphMetricRoot_inverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))).symm

theorem coulombAuxiliaryMinimalGraph_original_datum {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {q : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, coulombInverseRootL2L N β q) ∈ coulombAuxiliaryMinimalGraph N hβ) :
    (f, q) ∈ coulombMaxDbarGraph hβ :=
  coulombAuxiliaryMinimalGraph_original_graph hβ hfg (coulombInverseRootL2_raw_identity β q)

end RepulsiveCoulomb
