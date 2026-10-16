module

public import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal
public import LeanResearch.RepulsiveCoulomb.CoulombPermutation
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! Permutation symmetry of Gibbs-L2 classes becomes pointwise symmetry of
continuous (in particular genuinely holomorphic) collision-free representatives. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem poleBranch_coulomb_symmetry_pointwise
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    {f : CoulombConfig N → ℂ} (hf : ContinuousOn f (coulombDomain N))
    (hs : (fun z => f (coulombPermute σ z)) =ᵐ[coulombMeasure N β] f) :
    ∀ z ∈ coulombDomain N, f (coulombPermute σ z) = f z := by
  have hv : (fun z => f (coulombPermute σ z)) =ᵐ[volume] f :=
    (coulombMeasure_ae_iff hβ).mp hs
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hv) (coulombDomain N).isOpen
    (hf.comp (coulombPermute σ).continuous.continuousOn
      (fun z hz => (coulombPermute_mem_domain σ z).mpr hz)) hf

theorem poleBranch_coulomb_symmetry_of_representative
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    {f h : CoulombConfig N → ℂ} (hf : DifferentiableOn ℂ f (coulombDomain N))
    (hfh : f =ᵐ[coulombMeasure N β] h)
    (hs : (fun z => h (coulombPermute σ z)) =ᵐ[coulombMeasure N β] h) :
    ∀ z ∈ coulombDomain N, f (coulombPermute σ z) = f z := by
  apply poleBranch_coulomb_symmetry_pointwise hβ σ hf.continuousOn
  have ht := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae_eq_comp hfh
  exact ht.trans (hs.trans hfh.symm)

end RepulsiveCoulomb
