module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeakSystemTests

@[expose] public section

/-! The combined weak system commutes with interior convolution up to the
literal finite sum of Friedrichs kernels. This uses the joint weak equation
and does not require separate weak derivatives of individual input entries. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology Convolution Distributions BigOperators
namespace RepulsiveCoulomb

theorem dbarLp_fintypeSum_coe {N : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (F : ι → CoulombConfig N → ℂ) (hF : ∀ i, f i =ᵐ[volume] F i) :
    (∑ i, f i) =ᵐ[volume] fun z => ∑ i, F i z := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ f, ae_all_iff.mpr hF] with z hz hFz
  rw [hz]
  exact Finset.sum_congr rfl (fun i _ => hFz i)

theorem dbarWeakSystem_reflected_equation {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v u g)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (a : κ) (z : CoulombConfig N) :
    (∫ x, ψ (z - x) • g a x) =
      (∑ b, ∑ d, ((∫ x, dbarRealKernelDerivative (v d) ψ (z - x) • (A a b d x * u b x)) -
        ∫ x, ψ (z - x) • (dbarVolumeCoreDerivative (v d) (A a b d) x * u b x))) +
        ∑ b, ∫ x, ψ (z - x) • (B a b x * u b x) := by
  have h := hweak a (dbarReflectedKernelTest ψ z)
  simp_rw [dbarWeakSystem_reflected_term] at h
  change (∫ x, ψ (z - x) • g a x) = _ at h
  convert h using 1
  simp only [← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  abel

theorem dbarWeakSystem_kernel_equation {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v u g)
    (hg : ∀ a, Integrable (g a : CoulombConfig N → ℂ) volume)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (a : κ) :
    dbarVolumeKernelLp ψ (g a) =
      (∑ b, ∑ d,
        (dbarVolumeKernelLp (dbarRealKernelDerivative (v d) ψ)
          (dbarVolumeMulL ((A a b d).memLp_top (μ := volume)) (u b)) -
        dbarVolumeKernelLp ψ
          (dbarVolumeMulL ((dbarVolumeCoreDerivative (v d) (A a b d)).memLp_top (μ := volume)) (u b)))) +
      ∑ b, dbarVolumeKernelLp ψ (dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (u b)) := by
  let Q := fun b d =>
    dbarVolumeKernelLp (dbarRealKernelDerivative (v d) ψ)
      (dbarVolumeMulL ((A a b d).memLp_top (μ := volume)) (u b)) -
    dbarVolumeKernelLp ψ
      (dbarVolumeMulL ((dbarVolumeCoreDerivative (v d) (A a b d)).memLp_top (μ := volume)) (u b))
  let F := fun b d z =>
    (∫ x, dbarRealKernelDerivative (v d) ψ (z - x) • (A a b d x * u b x)) -
      ∫ x, ψ (z - x) • (dbarVolumeCoreDerivative (v d) (A a b d) x * u b x)
  have hQ (b : ι) (d : δ) : Q b d =ᵐ[volume] F b d := by
    filter_upwards [Lp.coeFn_sub
        (dbarVolumeKernelLp (dbarRealKernelDerivative (v d) ψ)
          (dbarVolumeMulL ((A a b d).memLp_top (μ := volume)) (u b)))
        (dbarVolumeKernelLp ψ
          (dbarVolumeMulL ((dbarVolumeCoreDerivative (v d) (A a b d)).memLp_top (μ := volume)) (u b))),
      dbarVolumeKernelLp_mul_coe_reflected (dbarRealKernelDerivative (v d) ψ) (A a b d) (u b),
      dbarVolumeKernelLp_mul_coe_reflected ψ (dbarVolumeCoreDerivative (v d) (A a b d)) (u b)] with z hz hA hDA
    change (Q b d) z = F b d z
    simp only [Q, F, hz, Pi.sub_apply, hA, hDA]
  have hQs := dbarLp_fintypeSum_coe (fun b => ∑ d, Q b d) (fun b z => ∑ d, F b d z)
    (fun b => dbarLp_fintypeSum_coe (Q b) (F b) (hQ b))
  have hBs := dbarLp_fintypeSum_coe
    (fun b => dbarVolumeKernelLp ψ (dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (u b)))
    (fun b z => ∫ x, ψ (z - x) • (B a b x * u b x))
    (fun b => dbarVolumeKernelLp_mul_coe_reflected ψ (B a b) (u b))
  apply Lp.ext
  filter_upwards [dbarVolumeKernelLp_coe_reflected ψ (g a) (hg a), hQs, hBs,
    Lp.coeFn_add (∑ b, ∑ d, Q b d)
      (∑ b, dbarVolumeKernelLp ψ (dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (u b)))]
    with z hgq hq hb hadd
  rw [hgq, hadd, Pi.add_apply, hq, hb]
  exact dbarWeakSystem_reflected_equation A B v u g hweak ψ a z

end RepulsiveCoulomb
