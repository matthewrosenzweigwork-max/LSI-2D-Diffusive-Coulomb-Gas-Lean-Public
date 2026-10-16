module

public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalSystemUniqueness
public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactIntegrationByParts

@[expose] public section

/-! Actual compact smooth inputs satisfy the literal local first-order weak
system with their classical outputs. The coefficient product is a genuine
compact test even when the coefficient is smooth only on Omega. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombLocalCoefficient_directional_ibp {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (v : CoulombConfig N) :
    (∫ z, φ z • (a z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z v)) =
      -(∫ z, ((fderiv ℝ (φ : CoulombConfig N → ℝ) z v) • a z +
        φ z • fderiv ℝ a z v) * ψ z) := by
  let q := coulombComplexCoreMulLocal a ha (TestFunction.postcompCLM Complex.ofRealCLM φ)
  have h := dbarComplexCore_directional_ibp q ψ v
  have hleft : (∫ z, q z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z v) =
      ∫ z, φ z • (a z * fderiv ℝ (ψ : CoulombConfig N → ℂ) z v) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only [q]
      change (a z * (φ z : ℂ)) * _ = _
      rw [Complex.real_smul]
      ring
  have hright : (∫ z, fderiv ℝ (q : CoulombConfig N → ℂ) z v * ψ z) =
      ∫ z, ((fderiv ℝ (φ : CoulombConfig N → ℝ) z v) • a z +
        φ z • fderiv ℝ a z v) * ψ z := by
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only [q]
      rw [coulombComplexCoreMulLocal_fderiv_apply, coulombRealCore_complex_fderiv]
      change (a z * (fderiv ℝ (φ : CoulombConfig N → ℝ) z v : ℂ) +
        (φ z : ℂ) * fderiv ℝ a z v) * ψ z = _
      simp only [Complex.real_smul]
      ring
  rw [hleft, hright] at h
  exact h

def coulombLocalSystemCoreOutput {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (ψ : ι → TestFunction (coulombDomain N) ℂ ⊤) (a : κ) :
    TestFunction (coulombDomain N) ℂ ⊤ :=
  (∑ b, ∑ d, coulombComplexCoreMulLocal (A a b d) (hA a b d)
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (v d) (ψ b))) +
      ∑ b, coulombComplexCoreMulLocal (B a b) (hB a b) (ψ b)

theorem coulombLocalSystemCoreOutput_apply {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (ψ : ι → TestFunction (coulombDomain N) ℂ ⊤)
    (a : κ) (z : CoulombConfig N) :
    coulombLocalSystemCoreOutput A B hA hB v ψ a z =
      (∑ b, ∑ d, A a b d z * fderiv ℝ (ψ b : CoulombConfig N → ℂ) z (v d)) +
        ∑ b, B a b z * ψ b z := by
  simp only [coulombLocalSystemCoreOutput, _root_.add_apply, _root_.sum_apply,
    coulombComplexCoreMulLocal_apply, coulombComplexCore_lineDeriv_apply]

theorem coulombLocalSystemCoreOutput_weakSystem {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (ψ : ι → TestFunction (coulombDomain N) ℂ ⊤) :
    DbarLocalWeakSystem A B v (fun b => (ψ b : CoulombConfig N → ℂ))
      (fun a => (coulombLocalSystemCoreOutput A B hA hB v ψ a : CoulombConfig N → ℂ)) := by
  intro a φ
  have hI (b : ι) (d : δ) : Integrable (fun z => φ z •
      (A a b d z * fderiv ℝ (ψ b : CoulombConfig N → ℂ) z (v d))) volume := by
    let q := coulombComplexCoreMulLocal (A a b d) (hA a b d)
      (TestFunction.postcompCLM Complex.ofRealCLM φ)
    apply (dbarComplexCore_directional_product_integrable q (ψ b) (v d)).congr
    exact Eventually.of_forall fun z => by
      dsimp only [q]
      change (A a b d z * (φ z : ℂ)) * _ = _
      rw [Complex.real_smul]
      ring
  have hJ (b : ι) : Integrable (fun z => φ z • (B a b z * ψ b z)) volume :=
    coulombLocalCoefficient_test_integrable (B a b) (hB a b) φ
      (((ψ b).continuous.locallyIntegrable).locallyIntegrableOn _)
  simp_rw [coulombLocalSystemCoreOutput_apply, smul_add, Finset.smul_sum]
  rw [integral_add
    (integrable_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ (fun d _ => hI b d)))
    (integrable_finsetSum Finset.univ (fun b _ => hJ b)),
    integral_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ (fun d _ => hI b d)),
    integral_finsetSum Finset.univ (fun b _ => hJ b)]
  have hibp (b : ι) (d : δ) :=
    coulombLocalCoefficient_directional_ibp (A a b d) (hA a b d) φ (ψ b) (v d)
  simp_rw [integral_finsetSum Finset.univ (fun d _ => hI _ d),
    hibp, Finset.sum_neg_distrib]

end RepulsiveCoulomb
