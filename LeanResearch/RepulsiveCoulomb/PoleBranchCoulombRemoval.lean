module

public import LeanResearch.RepulsiveCoulomb.PoleBranchGenericCollisionRemoval
public import LeanResearch.RepulsiveCoulomb.PoleBranchOpenExtensionGlue
public import LeanResearch.RepulsiveCoulomb.PoleBranchHolomorphicSymmetry

@[expose] public section

/-! The manuscript collision-removal statement, with the genuine original
holomorphic class, actual normalized Gibbs L2 integrability, a.e. permutation
symmetry, the endpoint exponent two, and all simultaneous collisions. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

theorem poleBranch_coulomb_weighted_symmetric_removable
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    {f : CoulombConfig N → ℂ} (hf : DifferentiableOn ℂ f (coulombDomain N))
    (hi : MemLp f 2 (coulombMeasure N β))
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      (fun z => f (coulombPermute σ z)) =ᵐ[coulombMeasure N β] f) :
    ∃ F : CoulombConfig N → ℂ, Differentiable ℂ F ∧ EqOn F f (coulombDomain N) := by
  have hsym' : ∀ σ : Equiv.Perm (Fin N), ∀ z ∈ coulombDomain N,
      f (coulombPermute σ z) = f z :=
    fun σ => poleBranch_coulomb_symmetry_pointwise hβ σ hf.continuousOn (hsym σ)
  have hlocal : ∀ z ∈ poleBranchCoulombRegular N,
      ∃ U : Set (CoulombConfig N), IsOpen U ∧ z ∈ U ∧
        ∃ g : CoulombConfig N → ℂ, DifferentiableOn ℂ g U ∧
          EqOn g f (U ∩ coulombDomain N) := by
    intro z hz
    by_cases hzD : z ∈ coulombDomain N
    · exact ⟨coulombDomain N, (coulombDomain N).isOpen, hzD, f, hf, fun _ _ => rfl⟩
    · obtain ⟨p, hp, hpc, hpo⟩ := poleBranch_generic_collision_pair hz hzD
      have hN : 2 ≤ N := by
        have hlt := (mem_coulombPairs p).mp hp
        have hbound := p.2.isLt
        omega
      obtain ⟨M, hM⟩ : ∃ M : ℕ, N = M + 2 := ⟨N - 2, by omega⟩
      subst N
      exact poleBranch_generic_collision_removable hβ ha2 hf hi hsym' p hp z hpc hpo
  obtain ⟨g, hg, hgf⟩ := poleBranch_glue_local_extensions_on_open
    (poleBranch_coulombDomain_dense N) (poleBranchCoulombRegular_isOpen N) hlocal
  obtain ⟨F, hF, hFg⟩ := poleBranch_coulomb_multiple_collision_removable hg
  refine ⟨F, hF, ?_⟩
  intro z hz
  have hreg := poleBranch_coulombDomain_subset_regular N hz
  exact (hFg hreg).trans (hgf ⟨hreg, hz⟩)

theorem poleBranch_coulomb_entire_representative
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (ha2 : β / (N : ℝ) ≤ 2)
    {f : CoulombConfig N → ℂ} (hf : DifferentiableOn ℂ f (coulombDomain N))
    (hi : MemLp f 2 (coulombMeasure N β))
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      (fun z => f (coulombPermute σ z)) =ᵐ[coulombMeasure N β] f) :
    ∃ F : CoulombConfig N → ℂ, Differentiable ℂ F ∧ MemLp F 2 (coulombMeasure N β) ∧
      F =ᵐ[coulombMeasure N β] f := by
  obtain ⟨F, hF, hEq⟩ := poleBranch_coulomb_weighted_symmetric_removable hβ ha2 hf hi hsym
  have hae : F =ᵐ[coulombMeasure N β] f := by
    filter_upwards [(coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz
    exact hEq hz
  exact ⟨F, hF, (memLp_congr_ae hae).mpr hi, hae⟩

end RepulsiveCoulomb
