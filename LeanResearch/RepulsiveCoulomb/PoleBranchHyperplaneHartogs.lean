import LeanResearch.RepulsiveCoulomb.PoleBranchFiniteGraphHartogs
import LeanResearch.RepulsiveCoulomb.PoleBranchLinearSplit

/-! Hartogs removal for pairwise intersections in a finite family of distinct
complex hyperplanes, expressed in the original ambient vector space. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def poleBranchHyperplaneRegular {ι X : Type*} (ℓ : ι → X → ℂ) : Set X :=
  {x | ∀ i j, i ≠ j → ℓ i x ≠ 0 ∨ ℓ j x ≠ 0}

theorem poleBranch_finite_hyperplane_hartogs
    {ι X : Type*} [Finite ι] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [FiniteDimensional ℂ X] (ℓ : ι → X →L[ℂ] ℂ)
    (hℓ : ∀ i, ℓ i ≠ 0) (hker : Function.Injective (fun i => (ℓ i).ker))
    {f : X → ℂ} (hf : DifferentiableOn ℂ f (poleBranchHyperplaneRegular (fun i => ℓ i))) :
    ∃ F : X → ℂ, Differentiable ℂ F ∧ EqOn F f (poleBranchHyperplaneRegular (fun i => ℓ i)) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
      letI := he
      have hV : poleBranchHyperplaneRegular (fun i => ℓ i) = univ := by
        ext x
        simp [poleBranchHyperplaneRegular]
      exact ⟨f, differentiableOn_univ.mp (hV ▸ hf), fun _ _ => rfl⟩
  | inr he =>
      letI := he
      letI : ProperSpace X := FiniteDimensional.proper ℂ X
      have hd : Dense (⋂ i, {x : X | ℓ i x ≠ 0}) :=
        dense_iInter_of_isOpen
          (fun i => isOpen_ne.preimage (ℓ i).continuous)
          (fun i => poleBranch_dense_nonzero_linear (ℓ i) (hℓ i))
      obtain ⟨v, hv⟩ := hd.nonempty
      have hv' : ∀ i, ℓ i v ≠ 0 := fun i => mem_iInter.mp hv i
      let i₀ : ι := Classical.choice he
      let q : X →L[ℂ] ℂ := (ℓ i₀ v)⁻¹ • ℓ i₀
      have hq : q v = 1 := by simp [q, hv' i₀]
      let e := poleBranchLinearSplit q v hq
      let L : ι → q.ker →L[ℂ] ℂ := fun i => poleBranchHyperplaneHeight q (ℓ i) v
      have hzero (i : ι) (p : q.ker × ℂ) : ℓ i (e.symm p) = 0 ↔ p.2 = L i p.1 :=
        poleBranchHyperplaneHeight_zero_iff q (ℓ i) v (hv' i) p
      have hLi : Function.Injective L := by
        intro i j hij
        apply hker
        apply Submodule.ext
        intro x
        change ℓ i x = 0 ↔ ℓ j x = 0
        rw [← e.symm_apply_apply x, hzero i, hzero j, hij]
      have hreg (p : q.ker × ℂ) :
          e.symm p ∈ poleBranchHyperplaneRegular (fun i => ℓ i) ↔
            p ∈ poleBranchGraphRegular (fun i => L i) := by
        simp only [poleBranchHyperplaneRegular, poleBranchGraphRegular, mem_setOf_eq,
          ne_eq, hzero]
      have hfc : DifferentiableOn ℂ (fun p => f (e.symm p))
          (poleBranchGraphRegular (fun i => L i)) :=
        hf.comp e.symm.differentiableOn (fun p hp => (hreg p).mpr hp)
      obtain ⟨F, hF, hEq⟩ := poleBranch_finite_graph_hartogs L hLi hfc
      refine ⟨fun x => F (e x), hF.comp e.differentiable, ?_⟩
      intro x hx
      have heq := hEq ((hreg (e x)).mp (by simpa only [e.symm_apply_apply] using hx))
      simpa only [e.symm_apply_apply] using heq

end RepulsiveCoulomb
