module

public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalSystemExtension

@[expose] public section

/-! Literal conversion of a local weak divergence system to the combined
first-order system used by the one-sequence Friedrichs argument. The input
has only local integrability; no separate component derivative is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombLocalCoefficient_test_integrable {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    {u : CoulombConfig N → ℂ} (hu : LocallyIntegrableOn u (coulombDomain N) volume) :
    Integrable (fun z => φ z • (a z * u z)) volume := by
  have h := (coulombComplexCoreMulLocal a ha
    (TestFunction.postcompCLM Complex.ofRealCLM φ)).integrable_bilin
      (ContinuousLinearMap.mul ℝ ℂ) hu
  convert h using 1
  ext z
  change φ z • (a z * u z) = (a z * (φ z : ℂ)) * u z
  rw [Complex.real_smul]
  ring

def DbarLocalWeakDivergenceSystem {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ)
    (g : κ → CoulombConfig N → ℂ) : Prop :=
  ∀ a (φ : TestFunction (coulombDomain N) ℝ ⊤), (∫ x, φ x • g a x) =
    -(∑ b, ∑ d, ∫ x, (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) •
      (A a b d x * u b x)) + ∑ b, ∫ x, φ x • (B a b x * u b x)

def dbarDivergenceLowerCoefficient {N : ℕ} {ι κ δ : Type*} [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (v : δ → CoulombConfig N) (a : κ) (b : ι) (x : CoulombConfig N) : ℂ :=
  B a b x + ∑ d, fderiv ℝ (A a b d) x (v d)

theorem dbarDivergenceLowerCoefficient_contDiffAt {N : ℕ} {ι κ δ : Type*} [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (a : κ) (b : ι) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (dbarDivergenceLowerCoefficient A B v a b) z := by
  apply (hB a b z hz).add
  apply ContDiffAt.sum
  intro d _
  exact ((hA a b d z hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

theorem dbarLocalWeakDivergenceSystem_to_weakSystem {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ)
    (g : κ → CoulombConfig N → ℂ)
    (hu : ∀ b, LocallyIntegrableOn (u b) (coulombDomain N) volume)
    (hweak : DbarLocalWeakDivergenceSystem A B v u g) :
    DbarLocalWeakSystem A (dbarDivergenceLowerCoefficient A B v) v u g := by
  intro a φ
  have hder (b : ι) (d : δ) :
      Integrable (fun x => φ x • (fderiv ℝ (A a b d) x (v d) * u b x)) volume := by
    apply coulombLocalCoefficient_test_integrable _ _ φ (hu b)
    intro z hz
    exact ((hA a b d z hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have htest (b : ι) (d : δ) :
      Integrable (fun x => (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) •
        (A a b d x * u b x)) volume := by
    have h := coulombLocalCoefficient_test_integrable (A a b d) (hA a b d)
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (v d) φ) (hu b)
    convert h using 1
    ext x
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) φ (by simp)]
  have hzero (b : ι) := coulombLocalCoefficient_test_integrable (B a b) (hB a b) φ (hu b)
  have hfirst (b : ι) (d : δ) :
      (∫ x, ((fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) • A a b d x +
        φ x • fderiv ℝ (A a b d) x (v d)) * u b x) =
      (∫ x, (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) • (A a b d x * u b x)) +
        ∫ x, φ x • (fderiv ℝ (A a b d) x (v d) * u b x) := by
    calc
      _ = ∫ x, (fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) • (A a b d x * u b x) +
          φ x • (fderiv ℝ (A a b d) x (v d) * u b x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by simp only [Complex.real_smul]; ring
      _ = _ := integral_add (htest b d) (hder b d)
  have hcorrect (b : ι) :
      (∫ x, φ x • (dbarDivergenceLowerCoefficient A B v a b x * u b x)) =
        (∫ x, φ x • (B a b x * u b x)) +
          ∑ d, ∫ x, φ x • (fderiv ℝ (A a b d) x (v d) * u b x) := by
    calc
      _ = ∫ x, φ x • (B a b x * u b x) +
          ∑ d, φ x • (fderiv ℝ (A a b d) x (v d) * u b x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [dbarDivergenceLowerCoefficient, add_mul, smul_add, Finset.sum_mul,
            Finset.smul_sum]
      _ = _ := by
        rw [integral_add (hzero b) (integrable_finsetSum Finset.univ (fun d _ => hder b d)),
          integral_finsetSum Finset.univ (fun d _ => hder b d)]
  simp_rw [hfirst, hcorrect, Finset.sum_add_distrib]
  rw [hweak a φ]
  abel

end RepulsiveCoulomb
