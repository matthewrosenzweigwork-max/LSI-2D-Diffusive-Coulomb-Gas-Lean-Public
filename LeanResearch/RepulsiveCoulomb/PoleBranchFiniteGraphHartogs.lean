import LeanResearch.RepulsiveCoulomb.PoleBranchHartogsCylinder
import LeanResearch.RepulsiveCoulomb.PoleBranchGraphGeometry
import LeanResearch.RepulsiveCoulomb.PoleBranchExtensionGlue

/-! A full several-variable Hartogs theorem for a finite union of pairwise
intersections of distinct complex-linear graph hyperplanes. No boundedness,
weighted-integrability, meromorphy, or extension premise is used here. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem poleBranch_finite_graph_hartogs
    {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (L : ι → E →L[ℂ] ℂ) (hL : Function.Injective L)
    {f : E × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (poleBranchGraphRegular (fun i => L i))) :
    ∃ F : E × ℂ → ℂ, Differentiable ℂ F ∧
      EqOn F f (poleBranchGraphRegular (fun i => L i)) := by
  let D : Set E := {p | Function.Injective (fun i => L i p)}
  have hD : Dense D := poleBranch_dense_distinct_linear_heights L hL
  have hV : IsOpen (poleBranchGraphRegular (fun i => L i)) :=
    poleBranch_graphRegular_isOpen _ (fun i => (L i).continuous)
  have hgood (p : E) (hp : p ∈ D) (z : ℂ) :
      (p, z) ∈ poleBranchGraphRegular (fun i => L i) := by
    intro i j hij
    by_cases hi : z = L i p
    · right
      intro hj
      exact hij (hp (hi.symm.trans hj))
    · exact Or.inl hi
  have hVdense : Dense (poleBranchGraphRegular (fun i => L i)) := by
    apply (hD.prod (dense_univ : Dense (univ : Set ℂ))).mono
    intro p hp
    exact hgood p.1 hp.1 p.2
  apply poleBranch_glue_local_extensions hVdense
  rintro ⟨p₀, z₀⟩
  obtain ⟨r, hr, havoid⟩ := poleBranch_exists_graph_contour (fun i => L i) p₀ z₀
  let U : Set E := {p | ∀ i, dist (L i p) z₀ ≠ r}
  have hU : IsOpen U := by
    simp only [U, setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_ne.preimage ((L i).continuous.dist continuous_const)
  have hp₀ : p₀ ∈ U := havoid
  have hc : ∀ p ∈ U, ∀ z ∈ sphere z₀ r,
      (p, z) ∈ poleBranchGraphRegular (fun i => L i) := by
    intro p hp z hz i j hij
    left
    intro hzi
    apply hp i
    simpa only [← hzi] using mem_sphere.mp hz
  have hdisc : ∀ p ∈ U ∩ D, ∀ z ∈ closedBall z₀ r,
      (p, z) ∈ poleBranchGraphRegular (fun i => L i) :=
    fun p hp z _ => hgood p hp.2 z
  have H := poleBranch_hartogs_cylinder hV hf hU hD hr hc hdisc
  exact ⟨U ×ˢ ball z₀ r, hU.prod isOpen_ball, ⟨hp₀, mem_ball_self hr⟩,
    poleBranchCauchyAt f z₀ r, H.1, H.2⟩

end RepulsiveCoulomb
