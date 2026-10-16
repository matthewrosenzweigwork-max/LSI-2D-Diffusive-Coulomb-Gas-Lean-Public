module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeakSystemConvolution

@[expose] public section

/-! One fixed mollifier family approximates a finite combined weak first-order
system in its value norm and all output norms simultaneously. Each coordinate
of each output uses the same parameter. Geometric cutoff and coefficient
identification for the auxiliary dbar system remain separate obligations. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def dbarSystemMollifiedOutput {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (a : κ) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (∑ b, ∑ d, dbarVolumeMulL ((A a b d).memLp_top (μ := volume))
    (dbarVolumeKernelLp (dbarRealKernelDerivative (v d) (dbarBumpKernelTest ψ)) (u b))) +
    ∑ b, dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (coulombVolumeLpMollify ψ (u b))

theorem dbarSystemMollifiedOutput_error {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v u g)
    (hg : ∀ a, Integrable (g a : CoulombConfig N → ℂ) volume)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (a : κ) :
    dbarSystemMollifiedOutput A B v u ψ a = coulombVolumeLpMollify ψ (g a) +
      (∑ b, ∑ d, dbarVolumeFriedrichsKernel ((A a b d).memLp_top (μ := volume))
        ((dbarVolumeCoreDerivative (v d) (A a b d)).memLp_top (μ := volume)) ψ (v d) (u b)) +
      ∑ b, (dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (coulombVolumeLpMollify ψ (u b)) -
        coulombVolumeLpMollify ψ (dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (u b))) := by
  have he := dbarWeakSystem_kernel_equation A B v u g hweak hg (dbarBumpKernelTest ψ) a
  simp only [dbarBumpKernelTest_mollifier] at he
  rw [he]
  simp only [dbarSystemMollifiedOutput, dbarVolumeFriedrichsKernel_split,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, dbarBumpKernelTest_mollifier]
  abel

theorem dbarSystemMollifiedOutput_tendsto {N : ℕ} {ι κ δ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ] {l : Filter η}
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v u g)
    (hg : ∀ a, Integrable (g a : CoulombConfig N → ℂ) volume)
    (ψ : ContDiffBump (0 : CoulombConfig N))
    (ε : η → ℝ) (hε : ∀ i, 0 < ε i) (hε0 : Tendsto ε l (𝓝 0)) (a : κ) :
    Tendsto (fun i => dbarSystemMollifiedOutput A B v u (dbarScaledBump ψ (hε i)) a)
      l (𝓝 (g a)) := by
  have hout : Tendsto (fun i => (dbarScaledBump ψ (hε i)).rOut) l (𝓝 0) := by
    simpa only [dbarScaledBump, zero_mul] using hε0.mul_const ψ.rOut
  have hk := tendsto_finsetSum Finset.univ (fun b _ =>
    tendsto_finsetSum Finset.univ (fun d _ =>
      dbarVolumeFriedrichsKernel_strong_tendsto (A a b d) ψ (v d) ε hε hε0 (u b)))
  have hb := tendsto_finsetSum Finset.univ (fun b _ =>
    dbarVolumeMollifier_mul_comm_tendsto ((B a b).memLp_top (μ := volume))
      (fun i => dbarScaledBump ψ (hε i)) hout (u b))
  have hm := coulombVolumeLpMollify_tendsto (fun i => dbarScaledBump ψ (hε i)) hout (g a)
  simp_rw [dbarSystemMollifiedOutput_error A B v u g hweak hg]
  simpa only [Finset.sum_const_zero, add_zero] using (hm.add hk).add hb

theorem dbarSystem_joint_mollification_tendsto {N : ℕ} {ι κ δ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ] {l : Filter η}
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v u g)
    (hg : ∀ a, Integrable (g a : CoulombConfig N → ℂ) volume)
    (ψ : ContDiffBump (0 : CoulombConfig N))
    (ε : η → ℝ) (hε : ∀ i, 0 < ε i) (hε0 : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => ((fun b => coulombVolumeLpMollify (dbarScaledBump ψ (hε i)) (u b)),
      (fun a => dbarSystemMollifiedOutput A B v u (dbarScaledBump ψ (hε i)) a)))
      l (𝓝 (u, g)) := by
  have hout : Tendsto (fun i => (dbarScaledBump ψ (hε i)).rOut) l (𝓝 0) := by
    simpa only [dbarScaledBump, zero_mul] using hε0.mul_const ψ.rOut
  exact (tendsto_pi_nhds.mpr fun b =>
    coulombVolumeLpMollify_tendsto (fun i => dbarScaledBump ψ (hε i)) hout (u b)).prodMk_nhds
    (tendsto_pi_nhds.mpr fun a =>
      dbarSystemMollifiedOutput_tendsto A B v u g hweak hg ψ ε hε hε0 a)

end RepulsiveCoulomb
