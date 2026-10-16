module

public import LeanResearch.RepulsiveCoulomb.DbarBranchHilbertAdjoint

@[expose] public section

/-! Actual adjoint-domain tests obtained by Riesz representation of the
already proved unweighted distributional pairings. These prove density of the
adjoint's value-domain. They do not assert any adjoint graph-core density. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions LinearPMap ComplexConjugate
namespace RepulsiveCoulomb

def coulombL2TestPairingComplexL {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : Lp ℂ 2 (coulombMeasure N β) →L[ℂ] ℂ where
  toFun := coulombL2TestPairingL hβ φ
  map_add' := map_add (coulombL2TestPairingL hβ φ)
  map_smul' := by
    intro c f
    change coulombL2TestPairingL hβ φ (c • f) = c • coulombL2TestPairingL hβ φ f
    rw [coulombL2TestPairingL_apply, coulombL2TestPairingL_apply,
      coulombL2Distribution_complex_smul_apply]
    rfl
  cont := (coulombL2TestPairingL hβ φ).continuous

theorem coulombL2TestPairingComplexL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombL2TestPairingComplexL hβ φ f = coulombL2Distribution hβ f φ :=
  coulombL2TestPairingL_apply hβ φ f

theorem coulombComplexCoordinateLp_eq {N : ℕ} {β : ℝ} (i : Fin N)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) g =
      (coulombCoordinate i).compLpL 2 (coulombMeasure N β) g := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g,
    (coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g] with z hc hr
  exact hc.trans hr.symm

def coulombDbarAdjointTestVector {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (InnerProductSpace.toDual ℂ _).symm
    ((coulombL2TestPairingComplexL hβ φ).comp ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β)))

def coulombDbarAdjointTestScalar {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : Lp ℂ 2 (coulombMeasure N β) :=
  (InnerProductSpace.toDual ℂ _).symm
    (-(1 / 2 : ℂ) •
      (coulombL2TestPairingComplexL hβ
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) +
        Complex.I • coulombL2TestPairingComplexL hβ
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)))

theorem coulombDbarAdjointTestVector_inner {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    inner ℂ (coulombDbarAdjointTestVector hβ i φ) g =
      coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) g) φ := by
  rw [coulombDbarAdjointTestVector, InnerProductSpace.toDual_symm_apply,
    ContinuousLinearMap.comp_apply, coulombComplexCoordinateLp_eq, coulombL2TestPairingComplexL_apply]

theorem coulombDbarAdjointTestScalar_inner {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    inner ℂ (coulombDbarAdjointTestScalar hβ i φ) f = -(1 / 2 : ℂ) *
      (coulombL2Distribution hβ f (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) +
        Complex.I * coulombL2Distribution hβ f
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)) := by
  rw [coulombDbarAdjointTestScalar, InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
    coulombL2TestPairingComplexL_apply]

theorem coulombDbarAdjointTest_mem_graph {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (coulombDbarAdjointTestVector hβ i φ, coulombDbarAdjointTestScalar hβ i φ) ∈
      (coulombMaxDbarAdjoint N hβ).graph := by
  apply (coulombMaxDbarAdjoint_graph_iff hβ _ _).mpr
  intro f k hfk
  have he : inner ℂ (coulombDbarAdjointTestVector hβ i φ) k =
      inner ℂ (coulombDbarAdjointTestScalar hβ i φ) f := by
    rw [coulombDbarAdjointTestVector_inner, coulombDbarAdjointTestScalar_inner]
    have hi := hfk i φ
    rw [coulombWeakDbarConstraintL_apply] at hi
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hi
    linear_combination hi
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) he

theorem coulombDbarAdjointTests_separate {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hg : ∀ i φ, inner ℂ (coulombDbarAdjointTestVector hβ i φ) g = 0) : g = 0 := by
  have hzero : coulombL2Distribution hβ (0 : Lp ℂ 2 (coulombMeasure N β)) = 0 :=
    map_zero (coulombL2DistributionLinear hβ ℂ)
  have hgraph : (0, g) ∈ coulombMaxDbarGraph hβ := by
    intro i φ
    rw [coulombWeakDbarConstraintL_apply, hzero]
    simp only [zero_apply, mul_zero, add_zero, smul_zero]
    rw [← coulombDbarAdjointTestVector_inner]
    exact hg i φ
  exact coulombMaxDbarGraph_unique hβ hgraph (coulombMaxDbarGraph hβ).zero_mem

theorem coulombMaxDbarAdjoint_dense_domain (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Dense ((coulombMaxDbarAdjoint N hβ).domain : Set (Lp (CoulombConfig N) 2 (coulombMeasure N β))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  apply coulombDbarAdjointTests_separate hβ g
  intro i φ
  exact hg (coulombDbarAdjointTestVector hβ i φ)
    (LinearPMap.mem_domain_of_mem_graph (coulombDbarAdjointTest_mem_graph hβ i φ))

end RepulsiveCoulomb
