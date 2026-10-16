module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactKernelRepresentation
public import LeanResearch.RepulsiveCoulomb.DbarBranchTranslationMultiplier
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! The actual compact smooth core in global Lebesgue L2, with directional
derivatives, products and density. This core will test the first-order
Friedrichs kernels before the uniform bound extends convergence to all L2. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace TopologicalSpace
open scoped NNReal Topology Distributions ComplexConjugate
namespace RepulsiveCoulomb

def dbarVolumeCoreValue {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ

theorem dbarVolumeCoreValue_coe {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    dbarVolumeCoreValue φ =ᵐ[volume] φ := MemLp.coeFn_toLp _

def dbarVolumeCoreValueLinear (N : ℕ) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (CoulombConfig N)) where
  toFun := dbarVolumeCoreValue
  map_add' := by
    intro φ ψ
    apply Lp.ext
    filter_upwards [dbarVolumeCoreValue_coe (φ + ψ), dbarVolumeCoreValue_coe φ,
      dbarVolumeCoreValue_coe ψ, Lp.coeFn_add (dbarVolumeCoreValue φ) (dbarVolumeCoreValue ψ)]
      with x hsum hφ hψ hadd
    simp only [hsum, hadd, Pi.add_apply, hφ, hψ]
    rfl
  map_smul' := by
    intro c φ
    change dbarVolumeCoreValue (c • φ) = c • dbarVolumeCoreValue φ
    apply Lp.ext
    filter_upwards [dbarVolumeCoreValue_coe (c • φ), dbarVolumeCoreValue_coe φ,
      Lp.coeFn_smul c (dbarVolumeCoreValue φ)] with x hsm hφ hc
    simp only [hsm, hc, Pi.smul_apply, hφ]
    rfl

def dbarVolumeCoreDerivative {N : ℕ} (v : CoulombConfig N)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
  TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ

theorem dbarVolumeCoreDerivative_apply {N : ℕ} (v : CoulombConfig N)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) (x : CoulombConfig N) :
    dbarVolumeCoreDerivative v φ x = fderiv ℝ (φ : CoulombConfig N → ℂ) x v := by
  rw [dbarVolumeCoreDerivative, TestFunction.lineDerivCLM_eq_fderivCLM]
  rw [TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) _ (by simp)]

def dbarVolumeCoreProduct {N : ℕ}
    (A φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
  ⟨fun x => A x * φ x, A.contDiff.mul φ.contDiff, A.hasCompactSupport.mul_right, subset_univ _⟩

theorem dbarVolumeCoreProduct_value {N : ℕ}
    (A φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    dbarVolumeCoreValue (dbarVolumeCoreProduct A φ) =
      dbarVolumeMulL (A.memLp_top (μ := volume)) (dbarVolumeCoreValue φ) := by
  apply Lp.ext
  filter_upwards [dbarVolumeCoreValue_coe (dbarVolumeCoreProduct A φ), dbarVolumeCoreValue_coe φ,
    dbarVolumeMulL_coe (A.memLp_top (μ := volume)) (dbarVolumeCoreValue φ)] with x hprod hφ hmul
  rw [hprod, hmul, hφ]
  rfl

theorem dbarVolumeCoreProduct_derivative {N : ℕ} (v : CoulombConfig N)
    (A φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    dbarVolumeCoreDerivative v (dbarVolumeCoreProduct A φ) =
      dbarVolumeCoreProduct A (dbarVolumeCoreDerivative v φ) +
        dbarVolumeCoreProduct (dbarVolumeCoreDerivative v A) φ := by
  ext x
  simp only [dbarVolumeCoreDerivative_apply, dbarVolumeCoreProduct]
  change (fderiv ℝ (fun y : CoulombConfig N => A y * φ y) x) v =
    A x * (fderiv ℝ (φ : CoulombConfig N → ℂ) x) v +
      (fderiv ℝ (A : CoulombConfig N → ℂ) x) v * φ x
  rw [fderiv_fun_mul (A.contDiff.differentiable (by simp) x) (φ.contDiff.differentiable (by simp) x)]
  simp [mul_comm]

theorem dbarVolumeCoreValue_annihilator {N : ℕ}
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : ∀ φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤,
      inner ℂ (dbarVolumeCoreValue φ) f = 0) : f = 0 := by
  have hloc : LocallyIntegrableOn (f : CoulombConfig N → ℂ)
      (⊤ : Opens (CoulombConfig N)) volume :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hzero := (⊤ : Opens (CoulombConfig N)).isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgΩ => by
      let φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤ := ⟨g, hg, hgc, hgΩ⟩
      let ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
      have he : (∫ z, g z • f z) = inner ℂ (dbarVolumeCoreValue ψ) f := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [dbarVolumeCoreValue_coe ψ] with z hz
        rw [hz]
        simp only [ψ, TestFunction.postcompCLM_apply, Function.comp_apply,
          Complex.ofRealCLM_apply, RCLike.inner_apply', Complex.conj_ofReal, Complex.real_smul]
        rfl
      exact he.trans (hf ψ))
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero] with x hx
  exact hx (mem_univ x)

theorem dbarVolumeCoreValue_denseRange (N : ℕ) : DenseRange (dbarVolumeCoreValue (N := N)) := by
  change Dense (LinearMap.range (dbarVolumeCoreValueLinear N) : Set (Lp ℂ 2 (volume : Measure (CoulombConfig N))))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  apply dbarVolumeCoreValue_annihilator f
  intro φ
  exact hf (dbarVolumeCoreValue φ) ⟨φ, rfl⟩

theorem dbarVolumeCore_lipschitz {N : ℕ}
    (A : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    ∃ C : ℝ≥0, LipschitzWith C (A : CoulombConfig N → ℂ) := by
  obtain ⟨C, hC⟩ := (A.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (A.hasCompactSupport.fderiv ℝ)
  let C' : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨C', lipschitzWith_of_nnnorm_fderiv_le (A.contDiff.differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast (hC x).trans (le_max_left C 0)

end RepulsiveCoulomb
