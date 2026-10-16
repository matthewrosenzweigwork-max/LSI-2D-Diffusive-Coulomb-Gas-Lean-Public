module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactDivergenceIdentity

@[expose] public section

/-! Genuine compact smooth vector values form a dense complex-linear subspace
of the fixed-fiber Gibbs vector L2 space. This is value-norm density only. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombComplexVectorCoreValue {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (dbarCoreVector_memLp hβ u).toLp (dbarCoreVector u)

theorem coulombComplexVectorCoreValue_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexVectorCoreValue hβ u =ᵐ[coulombMeasure N β] dbarCoreVector u := MemLp.coeFn_toLp _

def coulombComplexVectorCoreValueLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (Fin N → TestFunction (coulombDomain N) ℂ ⊤) →ₗ[ℂ]
      Lp (CoulombConfig N) 2 (coulombMeasure N β) where
  toFun := coulombComplexVectorCoreValue hβ
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [coulombComplexVectorCoreValue_coe hβ (u + v), coulombComplexVectorCoreValue_coe hβ u,
      coulombComplexVectorCoreValue_coe hβ v,
      Lp.coeFn_add (coulombComplexVectorCoreValue hβ u) (coulombComplexVectorCoreValue hβ v)] with z hsum hu hv hadd
    rw [hsum, hadd, Pi.add_apply, hu, hv]
    ext i
    rfl
  map_smul' := by
    intro c u
    change coulombComplexVectorCoreValue hβ (c • u) = c • coulombComplexVectorCoreValue hβ u
    apply Lp.ext
    filter_upwards [coulombComplexVectorCoreValue_coe hβ (c • u), coulombComplexVectorCoreValue_coe hβ u,
      Lp.coeFn_smul c (coulombComplexVectorCoreValue hβ u)] with z hsm hu hcoe
    rw [hsm, hcoe, Pi.smul_apply, hu]
    ext i
    rfl

theorem dbarCoreVector_single {N : ℕ} (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    dbarCoreVector (Pi.single i φ) z = EuclideanSpace.single i (φ z) := by
  classical
  ext j
  by_cases h : j = i <;> simp [dbarCoreVector, EuclideanSpace.single, h]

theorem coulombComplexVectorCoreValue_single_inner {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i : Fin N) (φ : TestFunction (coulombDomain N) ℂ ⊤)
    (f : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    inner ℂ (coulombComplexVectorCoreValue hβ (Pi.single i φ)) f =
      inner ℂ (coulombComplexCoreValue hβ φ)
        ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) f) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombComplexVectorCoreValue_coe hβ (Pi.single i φ),
    coulombComplexCoreValue_coe hβ φ,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) f]
    with z hv hφ hi
  rw [hv, hφ, hi, dbarCoreVector_single]
  simp only [EuclideanSpace.inner_single_left, RCLike.inner_apply']
  rfl

theorem coulombComplexVectorCoreValue_annihilator {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (hf : ∀ u : Fin N → TestFunction (coulombDomain N) ℂ ⊤,
      inner ℂ (coulombComplexVectorCoreValue hβ u) f = 0) : f = 0 := by
  have hcoord (i : Fin N) :
      (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) f = 0 := by
    apply coulombComplexCoreValue_annihilator hβ
    intro φ
    rw [← coulombComplexVectorCoreValue_single_inner hβ i φ f]
    exact hf _
  have hzero (i : Fin N) : (fun z => f z i) =ᵐ[coulombMeasure N β] 0 := by
    have hi := (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) f
    rw [hcoord i] at hi
    exact hi.symm.trans (Lp.coeFn_zero ℂ 2 (coulombMeasure N β))
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [ae_all_iff.mpr hzero] with z hz
  ext i
  exact hz i

theorem coulombComplexVectorCoreValue_denseRange (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DenseRange (coulombComplexVectorCoreValue (N := N) hβ) := by
  change Dense (LinearMap.range (coulombComplexVectorCoreValueLinear N hβ) :
    Set (Lp (CoulombConfig N) 2 (coulombMeasure N β)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  apply coulombComplexVectorCoreValue_annihilator hβ f
  intro u
  exact hf (coulombComplexVectorCoreValue hβ u) ⟨u, rfl⟩

end RepulsiveCoulomb
