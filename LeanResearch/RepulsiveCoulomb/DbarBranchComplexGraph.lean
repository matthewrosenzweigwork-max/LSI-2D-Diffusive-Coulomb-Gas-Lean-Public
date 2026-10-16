module

public import LeanResearch.RepulsiveCoulomb.DbarBranchDenseDomain

@[expose] public section

/-! Complex linearity of the actual maximal weak dbar graph. The underlying
closed set is unchanged; only its proved scalar structure is upgraded. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombL2Distribution_complex_smul_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (c : ℂ) (f : Lp ℂ 2 (coulombMeasure N β)) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombL2Distribution hβ (c • f) φ = c * coulombL2Distribution hβ f φ := by
  rw [coulombL2Distribution_apply, coulombL2Distribution_apply]
  calc
    _ = ∫ z, c * (φ z • f z) := by
      apply integral_congr_ae
      filter_upwards [(coulombMeasure_ae_iff hβ).mp (Lp.coeFn_smul c f)] with z hz
      rw [hz]
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      ring
    _ = _ := integral_const_mul _ _

theorem coulombCoordinateLp_complex_smul {N : ℕ} {β : ℝ} (i : Fin N) (c : ℂ)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    (coulombCoordinate i).compLpL 2 (coulombMeasure N β) (c • g) =
      c • (coulombCoordinate i).compLpL 2 (coulombMeasure N β) g := by
  apply Lp.ext
  filter_upwards [(coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) (c • g),
    (coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g,
    Lp.coeFn_smul c g,
    Lp.coeFn_smul c ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) g)] with z hcg hg hc hc'
  rw [hcg, hc, hc']
  simp only [Pi.smul_apply]
  rw [hg]
  exact map_smul (EuclideanSpace.proj i) c (g z)

theorem coulombWeakDbarConstraint_complex_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) (c : ℂ) (J : CoulombDbarL2Pair N β) :
    coulombWeakDbarConstraintL hβ i φ (c • J) = c * coulombWeakDbarConstraintL hβ i φ J := by
  rw [coulombWeakDbarConstraintL_apply, coulombWeakDbarConstraintL_apply]
  change coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) (c • J.2)) φ +
    (1 / 2 : ℝ) •
      (coulombL2Distribution hβ (c • J.1)
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) +
        Complex.I * coulombL2Distribution hβ (c • J.1)
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)) = _
  rw [coulombCoordinateLp_complex_smul]
  simp only [coulombL2Distribution_complex_smul_apply, Complex.real_smul]
  ring

def coulombMaxDbarComplexGraph {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Submodule ℂ (CoulombDbarL2Pair N β) where
  carrier := (coulombMaxDbarGraph (N := N) hβ : Set (CoulombDbarL2Pair N β))
  zero_mem' := (coulombMaxDbarGraph hβ).zero_mem
  add_mem' := (coulombMaxDbarGraph hβ).add_mem
  smul_mem' := by
    intro c J hJ
    change ∀ i φ, coulombWeakDbarConstraintL hβ i φ (c • J) = 0
    intro i φ
    rw [coulombWeakDbarConstraint_complex_smul, hJ i φ, mul_zero]

theorem coulombMaxDbarComplexGraph_isClosed {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    IsClosed (coulombMaxDbarComplexGraph (N := N) hβ : Set (CoulombDbarL2Pair N β)) :=
  coulombMaxDbarGraph_isClosed hβ

abbrev CoulombMaxDbarComplexDomain (N : ℕ) {β : ℝ} (hβ : 0 < β) :=
  coulombMaxDbarComplexGraph (N := N) hβ

instance coulombMaxDbarComplexDomain_completeSpace (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CompleteSpace (CoulombMaxDbarComplexDomain N hβ) :=
  (coulombMaxDbarComplexGraph_isClosed hβ).completeSpace_coe

def coulombMaxDbarComplexValueL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombMaxDbarComplexDomain N hβ →L[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (coulombMaxDbarComplexGraph hβ).subtypeL

def coulombMaxDbarComplexL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombMaxDbarComplexDomain N hβ →L[ℂ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (ContinuousLinearMap.snd ℂ _ _).comp (coulombMaxDbarComplexGraph hβ).subtypeL

theorem coulombMaxDbarComplexValueL_denseRange (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DenseRange (coulombMaxDbarComplexValueL N hβ) := by
  apply (coulombComplexCoreValue_denseRange N hβ).mono
  rintro f ⟨ψ, rfl⟩
  exact ⟨⟨(coulombComplexCoreValue hβ ψ, coulombComplexCoreDbar hβ ψ),
    coulombComplexCore_mem_maxDbarGraph hβ ψ⟩, rfl⟩

theorem coulombMaxDbarComplexValueL_injective (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Function.Injective (coulombMaxDbarComplexValueL N hβ) := by
  intro u v huv
  apply Subtype.ext
  apply Prod.ext
  · exact huv
  · have hu : (u.val.1, u.val.2) ∈ coulombMaxDbarGraph hβ := u.property
    have hv : (v.val.1, v.val.2) ∈ coulombMaxDbarGraph hβ := v.property
    change u.val.1 = v.val.1 at huv
    rw [← huv] at hv
    exact coulombMaxDbarGraph_unique hβ hu hv

end RepulsiveCoulomb
