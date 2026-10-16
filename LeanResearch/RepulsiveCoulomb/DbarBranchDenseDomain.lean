module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCoreCompatibility
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

/-! The maximal dbar operator has a dense value-domain in the weighted Hilbert
space. This only proves density for the L2 value norm, not graph-core density
for the maximal operator or its adjoint. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombComplexCoreValue_add {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexCoreValue hβ (φ + ψ) =
      coulombComplexCoreValue hβ φ + coulombComplexCoreValue hβ ψ := by
  apply Lp.ext
  filter_upwards [coulombComplexCoreValue_coe hβ (φ + ψ),
    coulombComplexCoreValue_coe hβ φ, coulombComplexCoreValue_coe hβ ψ,
    Lp.coeFn_add (coulombComplexCoreValue hβ φ) (coulombComplexCoreValue hβ ψ)] with z hsum hφ hψ hadd
  rw [hsum, hadd, Pi.add_apply, hφ, hψ]
  rfl

theorem coulombComplexCoreValue_complex_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (c : ℂ) (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexCoreValue hβ (c • φ) = c • coulombComplexCoreValue hβ φ := by
  apply Lp.ext
  filter_upwards [coulombComplexCoreValue_coe hβ (c • φ),
    coulombComplexCoreValue_coe hβ φ, Lp.coeFn_smul c (coulombComplexCoreValue hβ φ)] with z hsmul hφ hcoe
  rw [hsmul, hcoe, Pi.smul_apply, hφ]
  rfl

def coulombComplexCoreValueLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ] Lp ℂ 2 (coulombMeasure N β) where
  toFun := coulombComplexCoreValue hβ
  map_add' := coulombComplexCoreValue_add hβ
  map_smul' := coulombComplexCoreValue_complex_smul hβ

theorem coulombComplexCoreValue_annihilator {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β))
    (hf : ∀ ψ : TestFunction (coulombDomain N) ℂ ⊤,
      inner ℂ (coulombComplexCoreValue hβ ψ) f = 0) : f = 0 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hloc : LocallyIntegrableOn (f : CoulombConfig N → ℂ) (coulombDomain N) (coulombMeasure N β) :=
    (MemLp.integrable (by norm_num) (Lp.memLp f)).locallyIntegrable.locallyIntegrableOn _
  have hzero := (coulombDomain N).isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgΩ => by
      let φ : TestFunction (coulombDomain N) ℝ ⊤ := ⟨g, hg, hgc, hgΩ⟩
      let ψ : TestFunction (coulombDomain N) ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
      have he : (∫ z, g z • f z ∂coulombMeasure N β) =
          inner ℂ (coulombComplexCoreValue hβ ψ) f := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [coulombComplexCoreValue_coe hβ ψ] with z hz
        rw [hz]
        simp only [ψ, TestFunction.postcompCLM_apply, Function.comp_apply,
          Complex.ofRealCLM_apply, RCLike.inner_apply', Complex.conj_ofReal, Complex.real_smul]
        rfl
      exact he.trans (hf ψ))
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, (coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz hΩ
  exact hz hΩ

theorem coulombComplexCoreValue_denseRange (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DenseRange (coulombComplexCoreValue (N := N) hβ) := by
  change Dense (LinearMap.range (coulombComplexCoreValueLinear N hβ) : Set (Lp ℂ 2 (coulombMeasure N β)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  apply coulombComplexCoreValue_annihilator hβ f
  intro ψ
  exact hf (coulombComplexCoreValue hβ ψ) ⟨ψ, rfl⟩

theorem coulombMaxDbarValueL_denseRange (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DenseRange (coulombMaxDbarValueL N hβ) := by
  apply (coulombComplexCoreValue_denseRange N hβ).mono
  rintro f ⟨ψ, rfl⟩
  exact ⟨coulombMaxDbarCore hβ ψ, rfl⟩

end RepulsiveCoulomb
