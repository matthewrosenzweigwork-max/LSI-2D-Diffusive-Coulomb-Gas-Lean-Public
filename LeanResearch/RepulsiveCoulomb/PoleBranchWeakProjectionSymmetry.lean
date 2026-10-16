import LeanResearch.RepulsiveCoulomb.PoleBranchComplexLpAlgebra
import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelRegularity

/-! Symmetry and constants for the actual weak-kernel projection. This records-
only draft depends on the genuine weak-kernel regularity theorem, not on an
assumed smaller analytic class. It uses no curvature/distance estimate. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem poleBranch_weakKernel_permute {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    {v : Lp ℂ 2 (coulombMeasure N β)} (hv : v ∈ coulombDbarWeakKernel N hβ) :
    poleBranchComplexPermute N hβ σ v ∈ coulombDbarWeakKernel N hβ := by
  obtain ⟨H, hH, hrep⟩ := (coulombDbarWeakKernel_mem_iff_holomorphic hβ v).mp hv
  apply (coulombDbarWeakKernel_mem_iff_holomorphic hβ _).mpr
  refine ⟨fun z => H (coulombPermute σ z), ?_, ?_⟩
  · exact hH.comp (poleBranch_coulombPermute_differentiable σ).differentiableOn
      (fun z hz => (coulombPermute_mem_domain σ z).mpr hz)
  · have ht : (fun z => v (coulombPermute σ z)) =ᵐ[coulombMeasure N β]
        (fun z => H (coulombPermute σ z)) :=
      (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae_eq_comp hrep
    exact (poleBranchComplexPermute_coe hβ σ v).trans ht

theorem poleBranch_weakProjection_permute {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexPermute N hβ σ (coulombDbarWeakProjection N hβ v) =
      coulombDbarWeakProjection N hβ (poleBranchComplexPermute N hβ σ v) := by
  let K := (coulombDbarWeakKernel N hβ).toSubmodule
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (K := K) (poleBranch_weakKernel_permute hβ σ (coulombDbarWeakProjection_mem_kernel hβ v))
  intro w hw
  have hw' := poleBranch_weakKernel_permute hβ σ.symm hw
  have hback : poleBranchComplexPermute N hβ σ (poleBranchComplexPermute N hβ σ.symm w) = w := by
    simpa only [Equiv.symm_symm] using poleBranchComplexPermute_inverse hβ σ.symm w
  rw [← (poleBranchComplexPermute N hβ σ).map_sub, ← hback,
    (poleBranchComplexPermute N hβ σ).inner_map_map]
  exact Submodule.starProjection_inner_eq_zero v _ hw'

theorem poleBranch_weakProjection_invariant {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {v : Lp ℂ 2 (coulombMeasure N β)}
    (hv : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ v = v) :
    ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ (coulombDbarWeakProjection N hβ v) =
      coulombDbarWeakProjection N hβ v := by
  intro σ
  rw [poleBranch_weakProjection_permute, hv σ]

theorem poleBranchComplexOne_mem_kernel (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchComplexOne N hβ ∈ coulombDbarWeakKernel N hβ :=
  (coulombDbarWeakKernel_mem_iff_holomorphic hβ _).mpr
    ⟨fun _ => 1, differentiableOn_const 1, poleBranchComplexOne_coe N hβ⟩

theorem poleBranch_weakProjection_one (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombDbarWeakProjection N hβ (poleBranchComplexOne N hβ) = poleBranchComplexOne N hβ :=
  Submodule.starProjection_eq_self_iff.mpr (poleBranchComplexOne_mem_kernel N hβ)

def poleBranchComplexMean (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℂ 2 (coulombMeasure N β) →L[ℂ] ℂ := innerSL ℂ (poleBranchComplexOne N hβ)

theorem poleBranchComplexMean_eq_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexMean N hβ v = ∫ z, v z ∂coulombMeasure N β := by
  change inner ℂ (poleBranchComplexOne N hβ) v = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [poleBranchComplexOne_coe N hβ] with z hz
  rw [hz]
  simp

theorem poleBranch_weakProjection_mean {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℂ 2 (coulombMeasure N β)) :
    poleBranchComplexMean N hβ (coulombDbarWeakProjection N hβ v) = poleBranchComplexMean N hβ v := by
  change inner ℂ (poleBranchComplexOne N hβ) (coulombDbarWeakProjection N hβ v) = _
  have H := (coulombDbarWeakKernel N hβ).toSubmodule.inner_starProjection_left_eq_right
    (poleBranchComplexOne N hβ) v
  change inner ℂ (coulombDbarWeakProjection N hβ (poleBranchComplexOne N hβ)) v =
    inner ℂ (poleBranchComplexOne N hβ) (coulombDbarWeakProjection N hβ v) at H
  rw [poleBranch_weakProjection_one] at H
  exact H.symm

end RepulsiveCoulomb
