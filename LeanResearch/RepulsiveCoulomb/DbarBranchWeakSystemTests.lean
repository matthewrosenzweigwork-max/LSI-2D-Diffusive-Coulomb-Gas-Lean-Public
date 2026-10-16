module

public import LeanResearch.RepulsiveCoulomb.DbarBranchFriedrichsStrongConvergence

@[expose] public section

/-! Literal weak equations for one finite first-order system, with a single
input vector and all output components. No componentwise operator-domain
hypothesis is substituted for this joint system. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology Convolution Distributions BigOperators
namespace RepulsiveCoulomb

def dbarReflectedKernelTest {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (z : CoulombConfig N) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤ :=
  ⟨fun y => ψ (z - y), ψ.contDiff.comp (contDiff_const.sub contDiff_id),
    ψ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft z), subset_univ _⟩

theorem dbarReflectedKernelTest_derivative {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (z y v : CoulombConfig N) :
    dbarRealKernelDerivative v (dbarReflectedKernelTest ψ z) y =
      -dbarRealKernelDerivative v ψ (z - y) := by
  rw [dbarRealKernelDerivative_apply, dbarRealKernelDerivative_apply]
  change fderiv ℝ (fun w : CoulombConfig N => ψ (z - w)) y v = _
  have hd := (ψ.contDiff.differentiable (by simp) (z - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub z)
  have hfd := hd.fderiv
  change fderiv ℝ (fun w : CoulombConfig N => ψ (z - w)) y = _ at hfd
  rw [hfd]
  simp

theorem dbarVolumeKernelLp_coe_reflected {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : Integrable (f : CoulombConfig N → ℂ) volume) :
    dbarVolumeKernelLp ψ f =ᵐ[volume] fun z => ∫ y, ψ (z - y) • f y := by
  have h := dbarVolumeKernelLp_coe ψ f hf
  have he : (ψ : CoulombConfig N → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (f : CoulombConfig N → ℂ) =
      (f : CoulombConfig N → ℂ) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume]
        (ψ : CoulombConfig N → ℝ) := (convolution_flip _).symm
  exact h.trans (Eventually.of_forall fun z => by rw [he]; rfl)

theorem dbarVolumeCore_mul_integrable {N : ℕ}
    (A : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Integrable (fun x => A x * f x) volume :=
  A.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ)
    (((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn _)

theorem dbarVolumeCore_mulLp_integrable {N : ℕ}
    (A : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Integrable (dbarVolumeMulL (A.memLp_top (μ := volume)) f : CoulombConfig N → ℂ) volume :=
  (dbarVolumeCore_mul_integrable A f).congr
    (dbarVolumeMulL_coe (A.memLp_top (μ := volume)) f).symm

theorem dbarVolumeKernelLp_mul_coe_reflected {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (A : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeKernelLp ψ (dbarVolumeMulL (A.memLp_top (μ := volume)) f) =ᵐ[volume]
      fun z => ∫ y, ψ (z - y) • (A y * f y) := by
  refine (dbarVolumeKernelLp_coe_reflected ψ _ (dbarVolumeCore_mulLp_integrable A f)).trans ?_
  exact Eventually.of_forall fun z => integral_congr_ae
    ((dbarVolumeMulL_coe (A.memLp_top (μ := volume)) f).mono fun y hy => by
      dsimp only
      rw [hy])

def DbarVolumeWeakSystem {N : ℕ} {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N))) : Prop :=
  ∀ a (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤),
    (∫ x, φ x • g a x) =
      -(∑ b, ∑ d, ∫ x,
        ((dbarRealKernelDerivative (v d) φ x) • A a b d x +
          φ x • dbarVolumeCoreDerivative (v d) (A a b d) x) * u b x) +
        ∑ b, ∫ x, φ x • (B a b x * u b x)

theorem dbarWeakSystem_reflected_term {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (A : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (u : Lp ℂ 2 (volume : Measure (CoulombConfig N))) (z v : CoulombConfig N) :
    (∫ x, ((dbarRealKernelDerivative v (dbarReflectedKernelTest ψ z) x) • A x +
      dbarReflectedKernelTest ψ z x • dbarVolumeCoreDerivative v A x) * u x) =
      -(∫ x, dbarRealKernelDerivative v ψ (z - x) • (A x * u x)) +
        ∫ x, ψ (z - x) • (dbarVolumeCoreDerivative v A x * u x) := by
  have h₁ : Integrable (fun x => dbarRealKernelDerivative v ψ (z - x) • (A x * u x)) volume :=
    (dbarReflectedKernelTest (dbarRealKernelDerivative v ψ) z).integrable_smul
    ((dbarVolumeCore_mul_integrable A u).locallyIntegrable.locallyIntegrableOn _)
  have h₂ : Integrable (fun x => ψ (z - x) • (dbarVolumeCoreDerivative v A x * u x)) volume :=
    (dbarReflectedKernelTest ψ z).integrable_smul
    ((dbarVolumeCore_mul_integrable (dbarVolumeCoreDerivative v A) u).locallyIntegrable.locallyIntegrableOn _)
  calc
    _ = ∫ x, -(dbarRealKernelDerivative v ψ (z - x) • (A x * u x)) +
        ψ (z - x) • (dbarVolumeCoreDerivative v A x * u x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [dbarReflectedKernelTest_derivative]
        change (-dbarRealKernelDerivative v ψ (z - x) • A x +
          ψ (z - x) • dbarVolumeCoreDerivative v A x) * u x = _
        simp only [Complex.real_smul, Complex.ofReal_neg]
        ring
    _ = _ := by
      have hi := integral_add h₁.neg h₂
      simpa only [Pi.neg_apply, integral_neg] using hi

end RepulsiveCoulomb
