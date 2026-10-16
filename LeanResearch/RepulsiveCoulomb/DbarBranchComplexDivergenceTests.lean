import LeanResearch.RepulsiveCoulomb.DbarBranchLocalDivergenceSystem

/-! Complex compact tests for the literal local divergence equations. This
allows subsequent multiplication of a weak output by actual complex metric
coefficients, without assuming a componentwise derivative of the input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombComplexTestLinear_zero_of_real {N : ℕ}
    (L : TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ] ℂ)
    (hL : ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      L (TestFunction.postcompCLM Complex.ofRealCLM φ) = 0)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) : L ψ = 0 := by
  let ψr := TestFunction.postcompCLM Complex.reCLM ψ
  let ψi := TestFunction.postcompCLM Complex.imCLM ψ
  have he : ψ = TestFunction.postcompCLM Complex.ofRealCLM ψr +
      Complex.I • TestFunction.postcompCLM Complex.ofRealCLM ψi := by
    ext z
    change ψ z = ((ψ z).re : ℂ) + Complex.I * ((ψ z).im : ℂ)
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (ψ z)).symm
  rw [he, map_add, map_smul, hL ψr, hL ψi, smul_zero, add_zero]

theorem coulombLocalCoefficient_complex_test_integrable {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤)
    {u : CoulombConfig N → ℂ} (hu : LocallyIntegrableOn u (coulombDomain N) volume) :
    Integrable (fun z => ψ z * (a z * u z)) volume := by
  have h := (coulombComplexCoreMulLocal a ha ψ).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) hu
  convert h using 1
  ext z
  change ψ z * (a z * u z) = (a z * ψ z) * u z
  ring

def coulombLocalCoefficientComplexPairL {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (u : CoulombConfig N → ℂ) (hu : LocallyIntegrableOn u (coulombDomain N) volume) :
    TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ] ℂ where
  toFun ψ := ∫ z, ψ z * (a z * u z)
  map_add' ψ χ := by
    change (∫ z, (ψ z + χ z) * (a z * u z)) = _
    simp_rw [add_mul]
    exact integral_add (coulombLocalCoefficient_complex_test_integrable a ha ψ hu)
      (coulombLocalCoefficient_complex_test_integrable a ha χ hu)
  map_smul' c ψ := by
    change (∫ z, (c * ψ z) * (a z * u z)) = c * _
    simp_rw [mul_assoc]
    exact integral_const_mul c _

theorem coulombComplexCore_lineDeriv_apply {N : ℕ}
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (v z : CoulombConfig N) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v ψ) z =
      fderiv ℝ (ψ : CoulombConfig N → ℂ) z v := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) ψ (by simp)]

theorem coulombRealCore_complex_fderiv {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (v z : CoulombConfig N) :
    fderiv ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ : CoulombConfig N → ℂ) z v =
      (fderiv ℝ (φ : CoulombConfig N → ℝ) z v : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z
    (φ.contDiff.differentiable (by simp) z).hasFDerivAt
  have hfd := hd.fderiv
  change fderiv ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ : CoulombConfig N → ℂ) z = _ at hfd
  rw [hfd]
  rfl

theorem coulombComplexCoreMulLocal_fderiv_apply {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (z v : CoulombConfig N) :
    fderiv ℝ (coulombComplexCoreMulLocal a ha ψ : CoulombConfig N → ℂ) z v =
      a z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z v + ψ z * fderiv ℝ a z v := by
  by_cases hz : z ∈ coulombDomain N
  · have hd := ((ha z hz).differentiableAt (by simp)).hasFDerivAt.mul
      (ψ.contDiff.differentiable (by simp) z).hasFDerivAt
    change fderiv ℝ (a * (ψ : CoulombConfig N → ℂ)) z v = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  · have hzt : z ∉ tsupport (ψ : CoulombConfig N → ℂ) := fun h => hz (ψ.tsupport_subset h)
    have hψ := notMem_tsupport_iff_eventuallyEq.mp hzt
    have hm : (coulombComplexCoreMulLocal a ha ψ : CoulombConfig N → ℂ) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hψ] with x hx
      change a x * ψ x = 0
      rw [hx, Pi.zero_apply, mul_zero]
    rw [hm.fderiv_eq, hψ.fderiv_eq, hψ.eq_of_nhds]
    simp

theorem dbarLocalWeakDivergenceSystem_complex_test {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ)
    (g : κ → CoulombConfig N → ℂ)
    (hu : ∀ b, LocallyIntegrableOn (u b) (coulombDomain N) volume)
    (hg : ∀ a, LocallyIntegrableOn (g a) (coulombDomain N) volume)
    (hweak : DbarLocalWeakDivergenceSystem A B v u g)
    (a : κ) (ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    (∫ x, ψ x * g a x) =
      -(∑ b, ∑ d, ∫ x, fderiv ℝ (ψ : CoulombConfig N → ℂ) x (v d) *
        (A a b d x * u b x)) + ∑ b, ∫ x, ψ x * (B a b x * u b x) := by
  let L : TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ] ℂ :=
    coulombLocalCoefficientComplexPairL (fun _ => 1) (fun _ _ => contDiffAt_const) (g a) (hg a) +
      (∑ b, ∑ d, (coulombLocalCoefficientComplexPairL (A a b d) (hA a b d) (u b) (hu b)).comp
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (v d)).toLinearMap) -
      ∑ b, coulombLocalCoefficientComplexPairL (B a b) (hB a b) (u b) (hu b)
  have happ (χ : TestFunction (coulombDomain N) ℂ ⊤) :
      L χ = (∫ x, χ x * g a x) +
        (∑ b, ∑ d, ∫ x, fderiv ℝ (χ : CoulombConfig N → ℂ) x (v d) * (A a b d x * u b x)) -
          ∑ b, ∫ x, χ x * (B a b x * u b x) := by
    simp only [L, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    change (∫ x, χ x * (1 * g a x)) +
      (∑ b, ∑ d, ∫ x, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (v d) χ) x *
        (A a b d x * u b x)) - (∑ b, ∫ x, χ x * (B a b x * u b x)) = _
    simp only [one_mul, coulombComplexCore_lineDeriv_apply]
  have hL : ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      L (TestFunction.postcompCLM Complex.ofRealCLM φ) = 0 := by
    intro φ
    rw [happ]
    simp only [coulombRealCore_complex_fderiv]
    have h := hweak a φ
    simp only [Complex.real_smul] at h
    change (∫ x, (φ x : ℂ) * g a x) +
      (∑ b, ∑ d, ∫ x, (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d) : ℂ) *
        (A a b d x * u b x)) - (∑ b, ∫ x, (φ x : ℂ) * (B a b x * u b x)) = 0
    linear_combination h
  have h := coulombComplexTestLinear_zero_of_real L hL ψ
  rw [happ] at h
  linear_combination h

theorem dbarLocalWeakDivergenceSystem_coefficient_test {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ)
    (g : κ → CoulombConfig N → ℂ)
    (hu : ∀ b, LocallyIntegrableOn (u b) (coulombDomain N) volume)
    (hg : ∀ a, LocallyIntegrableOn (g a) (coulombDomain N) volume)
    (hweak : DbarLocalWeakDivergenceSystem A B v u g)
    (c : CoulombConfig N → ℂ)
    (hc : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) c z)
    (a : κ) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ x, φ x • (c x * g a x)) =
      -(∑ b, ∑ d, ∫ x,
        (c x * (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d) : ℂ) +
          (φ x : ℂ) * fderiv ℝ c x (v d)) * (A a b d x * u b x)) +
        ∑ b, ∫ x, φ x • (c x * (B a b x * u b x)) := by
  have h := dbarLocalWeakDivergenceSystem_complex_test A B hA hB v u g hu hg hweak a
    (coulombComplexCoreMulLocal c hc (TestFunction.postcompCLM Complex.ofRealCLM φ))
  simp_rw [coulombComplexCoreMulLocal_fderiv_apply, coulombRealCore_complex_fderiv] at h
  have hleft : (∫ x, (coulombComplexCoreMulLocal c hc
      (TestFunction.postcompCLM Complex.ofRealCLM φ)) x * g a x) =
        ∫ x, φ x • (c x * g a x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (c x * (φ x : ℂ)) * g a x = _
      dsimp only
      rw [Complex.real_smul]
      ring
  have hzero (b : ι) : (∫ x, (coulombComplexCoreMulLocal c hc
      (TestFunction.postcompCLM Complex.ofRealCLM φ)) x * (B a b x * u b x)) =
        ∫ x, φ x • (c x * (B a b x * u b x)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (c x * (φ x : ℂ)) * (B a b x * u b x) = _
      dsimp only
      rw [Complex.real_smul]
      ring
  rw [hleft] at h
  simp_rw [hzero] at h
  exact h

theorem dbarLocalWeakDivergenceSystem_output_combination {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ)
    (g : κ → CoulombConfig N → ℂ)
    (hu : ∀ b, LocallyIntegrableOn (u b) (coulombDomain N) volume)
    (hg : ∀ a, LocallyIntegrableOn (g a) (coulombDomain N) volume)
    (hweak : DbarLocalWeakDivergenceSystem A B v u g)
    (c : κ → CoulombConfig N → ℂ)
    (hc : ∀ a z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (c a) z)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ x, φ x • (∑ a, c a x * g a x)) =
      ∑ a, (-(∑ b, ∑ d, ∫ x,
        (c a x * (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d) : ℂ) +
          (φ x : ℂ) * fderiv ℝ (c a) x (v d)) * (A a b d x * u b x)) +
        ∑ b, ∫ x, φ x • (c a x * (B a b x * u b x))) := by
  calc
    _ = ∑ a, ∫ x, φ x • (c a x * g a x) := by
      simp_rw [Finset.smul_sum]
      exact integral_finsetSum Finset.univ
        (fun a _ => coulombLocalCoefficient_test_integrable (c a) (hc a) φ (hg a))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact dbarLocalWeakDivergenceSystem_coefficient_test A B hA hB v u g hu hg hweak
        (c a) (hc a) a φ

end RepulsiveCoulomb
