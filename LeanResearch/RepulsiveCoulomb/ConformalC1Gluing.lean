module

public import LeanResearch.RepulsiveCoulomb.PointConeSimilarity
public import Mathlib.Topology.Piecewise

@[expose] public section

/-! Elementary C1 gluing for the cone support functions. Both values and first
physical derivatives must agree on the interface. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_piecewise_equal_jet {s : Set E} [DecidablePred (· ∈ s)]
    {f g : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g A x) (heq : f x = g x) :
    HasFDerivAt (s.piecewise f g) A x := by
  have hval : s.piecewise f g x = f x := by
    by_cases hx : x ∈ s <;> simp [Set.piecewise, hx, heq]
  have hleft : HasFDerivWithinAt (s.piecewise f g) A s x :=
    hf.hasFDerivWithinAt.congr (fun u hu ↦ piecewise_eq_of_mem s f g hu) hval
  have hright : HasFDerivWithinAt (s.piecewise f g) A sᶜ x :=
    hg.hasFDerivWithinAt.congr (fun u hu ↦ piecewise_eq_of_notMem s f g hu) (hval.trans heq)
  simpa only [union_compl_self, hasFDerivWithinAt_univ] using hleft.union hright

theorem hasFDerivAt_piecewise_equal_frontier_jets {s : Set E} [DecidablePred (· ∈ s)]
    {f g : E → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hval : ∀ x ∈ frontier s, f x = g x)
    (hder : ∀ x ∈ frontier s, fderiv ℝ f x = fderiv ℝ g x) :
    ∀ x, HasFDerivAt (s.piecewise f g) (s.piecewise (fderiv ℝ f) (fderiv ℝ g) x) x := by
  intro x
  have hfx := (hf x).hasFDerivAt
  have hgx := (hg x).hasFDerivAt
  by_cases hx : x ∈ frontier s
  · have hd := hder x hx
    rw [← hd] at hgx
    have h := hasFDerivAt_piecewise_equal_jet (s := s) hfx hgx (hval x hx)
    by_cases hs : x ∈ s <;> simpa [Set.piecewise, hs, hd] using h
  · have hor : x ∈ interior s ∨ x ∈ interior sᶜ := by
      simpa only [frontier_eq_inter_compl_interior, mem_inter_iff, mem_compl_iff,
        not_and_or, not_not] using hx
    rcases hor with hs | hs
    · have he : s.piecewise f g =ᶠ[𝓝 x] f := by
        filter_upwards [isOpen_interior.mem_nhds hs] with u hu
        exact piecewise_eq_of_mem s f g (interior_subset hu)
      simpa only [piecewise_eq_of_mem s _ _ (interior_subset hs)] using hfx.congr_of_eventuallyEq he
    · have he : s.piecewise f g =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_interior.mem_nhds hs] with u hu
        exact piecewise_eq_of_notMem s f g (interior_subset hu)
      simpa only [piecewise_eq_of_notMem s _ _ (interior_subset hs)] using hgx.congr_of_eventuallyEq he


theorem contDiff_one_piecewise_equal_jets {s : Set E} [DecidablePred (· ∈ s)]
    {f g : E → F} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : ∀ x ∈ frontier s, f x = g x)
    (hder : ∀ x ∈ frontier s, fderiv ℝ f x = fderiv ℝ g x) :
    ContDiff ℝ 1 (s.piecewise f g) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨s.piecewise (fderiv ℝ f) (fderiv ℝ g), ?_, ?_⟩
  · exact Continuous.piecewise hder (contDiff_one_iff_fderiv.mp hf).2
      (contDiff_one_iff_fderiv.mp hg).2
  · exact hasFDerivAt_piecewise_equal_frontier_jets (hf.differentiable one_ne_zero)
      (hg.differentiable one_ne_zero) hval hder

end RepulsiveCoulomb
