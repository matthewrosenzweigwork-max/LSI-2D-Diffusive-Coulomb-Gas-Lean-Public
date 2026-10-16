import LeanResearch.RepulsiveCoulomb.PoleBranchWeakProjectionSymmetry
import LeanResearch.RepulsiveCoulomb.PoleBranchCoulombRemoval
import LeanResearch.RepulsiveCoulomb.CoulombPhaseIdentity

/-! The canonical conjugate-projection cancellation for centered symmetric
weak-kernel elements, using actual entire representatives and common-phase
integration. Endpoint beta/N=2 is retained. The genuine weak-kernel regularity
module is an explicit uncompiled dependency of this records-only draft. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem poleBranch_symmetric_kernel_entire {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ha2 : β / (N : ℝ) ≤ 2) (v : Lp ℂ 2 (coulombMeasure N β))
    (hv : v ∈ coulombDbarWeakKernel N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ v = v) :
    ∃ H : CoulombConfig N → ℂ, Differentiable ℂ H ∧ MemLp H 2 (coulombMeasure N β) ∧
      v =ᵐ[coulombMeasure N β] H := by
  obtain ⟨g, hg, hrep⟩ := (coulombDbarWeakKernel_mem_iff_holomorphic hβ v).mp hv
  have hL2 : MemLp g 2 (coulombMeasure N β) := (memLp_congr_ae hrep).mp (Lp.memLp v)
  have hgsym : ∀ σ : Equiv.Perm (Fin N), (fun z => g (coulombPermute σ z)) =ᵐ[coulombMeasure N β] g := by
    intro σ
    have hp := poleBranchComplexPermute_coe hβ σ v
    rw [hsym σ] at hp
    have ht : (fun z => v (coulombPermute σ z)) =ᵐ[coulombMeasure N β]
        (fun z => g (coulombPermute σ z)) :=
      (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae_eq_comp hrep
    filter_upwards [ht, hp, hrep] with z ht hp hv
    exact ht.symm.trans (hp.symm.trans hv)
  obtain ⟨H, hH, hiH, hHg⟩ := poleBranch_coulomb_entire_representative hβ ha2 hg hL2 hgsym
  exact ⟨H, hH, hiH, hrep.trans hHg.symm⟩

theorem poleBranch_centered_entire_value_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℂ 2 (coulombMeasure N β)) {H : CoulombConfig N → ℂ}
    (hH : Differentiable ℂ H) (hiH : MemLp H 2 (coulombMeasure N β))
    (hrep : v =ᵐ[coulombMeasure N β] H) (hmean : poleBranchComplexMean N hβ v = 0) : H 0 = 0 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hi : Integrable H (coulombMeasure N β) := MemLp.integrable (by norm_num) hiH
  rw [← coulomb_entire_integral hβ hH hi, ← integral_congr_ae hrep,
    ← poleBranchComplexMean_eq_integral]
  exact hmean

theorem poleBranch_weakProjection_conjugate_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ha2 : β / (N : ℝ) ≤ 2) (h : Lp ℂ 2 (coulombMeasure N β))
    (hh : h ∈ coulombDbarWeakKernel N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ h = h)
    (hmean : poleBranchComplexMean N hβ h = 0) :
    coulombDbarWeakProjection N hβ (poleBranchComplexConj N β h) = 0 := by
  let k := coulombDbarWeakProjection N hβ (poleBranchComplexConj N β h)
  have hk : k ∈ coulombDbarWeakKernel N hβ := coulombDbarWeakProjection_mem_kernel hβ _
  have hksym : ∀ σ : Equiv.Perm (Fin N), poleBranchComplexPermute N hβ σ k = k := by
    apply poleBranch_weakProjection_invariant hβ
    intro σ
    rw [poleBranchComplexConj_permute, hsym σ]
  obtain ⟨H, hH, hiH, hrep⟩ := poleBranch_symmetric_kernel_entire hβ ha2 h hh hsym
  obtain ⟨K, hK, hiK, hkrep⟩ := poleBranch_symmetric_kernel_entire hβ ha2 k hk hksym
  have hH0 := poleBranch_centered_entire_value_zero hβ h hH hiH hrep hmean
  have hprod : (fun z => inner ℂ (poleBranchComplexConj N β h z) (k z)) =ᵐ[coulombMeasure N β]
      fun z => H z * K z := by
    filter_upwards [poleBranchComplexConj_coe h, hrep, hkrep] with z hc hh hk
    rw [RCLike.inner_apply', hc, hh, hk]
    simp
  have hiHK : Integrable (fun z => H z * K z) (coulombMeasure N β) :=
    (L2.integrable_inner (𝕜 := ℂ) (poleBranchComplexConj N β h) k).congr hprod
  have hinner : inner ℂ (poleBranchComplexConj N β h) k = 0 := by
    rw [L2.inner_def, integral_congr_ae hprod, coulomb_common_phase_bilinear hβ hH hK hiHK, hH0, zero_mul]
  have ho := Submodule.starProjection_inner_eq_zero
    (K := (coulombDbarWeakKernel N hβ).toSubmodule) (poleBranchComplexConj N β h) k hk
  change inner ℂ (poleBranchComplexConj N β h - k) k = 0 at ho
  rw [inner_sub_left, hinner, zero_sub, neg_eq_zero] at ho
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp ho

end RepulsiveCoulomb
